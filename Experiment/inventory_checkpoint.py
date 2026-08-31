#!/usr/bin/env python3
"""Durable, opt-in checkpoints for deterministic inventory and scope batches.

The checkpoint format is deliberately small and self-describing.  A cache key
includes the ordered batch, source hashes, and the caller supplied immutable
toolchain/implementation identity.  Results are published only after the
producer returns successfully and the payload passes the same validator used
for cache hits.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
from collections.abc import Callable, Mapping, Sequence
from typing import Any


CHECKPOINT_SCHEMA = 1
_ENVELOPE_FIELDS = {
    "schema",
    "key",
    "inputs",
    "status",
    "payloadSha256",
    "payload",
}


def _canonical(value: object) -> bytes:
    """Encode JSON values in the stable form used for keys and digests."""
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as error:
        raise RuntimeError(f"checkpoint value is not stable JSON: {error}") from error


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _validate_identity(identity: Mapping[str, object]) -> dict[str, object]:
    # Round-tripping also rejects non-JSON values before a run can publish a
    # result whose key cannot be reconstructed later.
    encoded = _canonical(dict(identity))
    decoded = json.loads(encoded)
    if not isinstance(decoded, dict):
        raise RuntimeError("checkpoint identity must be a JSON object")
    return decoded


def _normalise_sources(
    modules: Sequence[str], source_hashes: Mapping[str, str] | Sequence[str]
) -> list[list[str]]:
    ordered_modules = list(modules)
    if any(not isinstance(module, str) or not module for module in ordered_modules):
        raise ValueError("checkpoint modules must be nonempty strings")
    if len(set(ordered_modules)) != len(ordered_modules):
        raise ValueError("checkpoint batch contains duplicate modules")
    if isinstance(source_hashes, Mapping):
        try:
            values = [source_hashes[module] for module in ordered_modules]
        except KeyError as error:
            raise ValueError(f"checkpoint source hash is missing: {error.args[0]}") from error
    else:
        values = list(source_hashes)
        if len(values) != len(ordered_modules):
            raise ValueError("checkpoint source hash count does not match modules")
    if any(not isinstance(value, str) or not value for value in values):
        raise ValueError("checkpoint source hashes must be nonempty strings")
    return [[module, value] for module, value in zip(ordered_modules, values)]


@dataclass(frozen=True)
class CheckpointResult:
    payload: Any
    hit: bool
    key: str


class CheckpointStore:
    """Read and atomically publish validated JSON batch results.

    ``root`` is opt-in: callers pass ``None`` to retain their old execution
    path and construct no store.  A malformed or stale entry is a miss with an
    explicit diagnostic; it is never returned to a caller.
    """

    def __init__(
        self,
        root: Path,
        *,
        identity: Mapping[str, object],
        diagnostic_stream: Any = None,
    ) -> None:
        self.root = Path(root)
        if self.root.is_symlink() or (self.root.exists() and not self.root.is_dir()):
            raise RuntimeError(f"checkpoint root must be a directory: {self.root}")
        self.identity = _validate_identity(identity)
        self.diagnostic_stream = diagnostic_stream if diagnostic_stream is not None else sys.stderr

    def _diagnostic(self, message: str) -> None:
        print(f"checkpoint: {message}", file=self.diagnostic_stream)

    def inputs(
        self,
        operation: str,
        modules: Sequence[str],
        source_hashes: Mapping[str, str] | Sequence[str],
        *,
        parameters: Mapping[str, object] | None = None,
    ) -> dict[str, object]:
        if not operation or "/" in operation or "\\" in operation:
            raise ValueError("checkpoint operation must be a simple nonempty name")
        input_parameters = {} if parameters is None else _validate_identity(parameters)
        return {
            "operation": operation,
            "modules": list(modules),
            "sourceHashes": _normalise_sources(modules, source_hashes),
            "identity": self.identity,
            "parameters": input_parameters,
        }

    def key_for(self, inputs: Mapping[str, object]) -> str:
        return sha256(_canonical({"schema": CHECKPOINT_SCHEMA, "inputs": dict(inputs)}))

    def path_for(self, key: str, operation: str) -> Path:
        if len(key) != 64 or any(character not in "0123456789abcdef" for character in key):
            raise ValueError("checkpoint key is not a SHA-256 digest")
        if not operation or "/" in operation or "\\" in operation:
            raise ValueError("checkpoint operation must be a simple nonempty name")
        return self.root / operation / f"{key}.json"

    def _validate_payload(
        self, payload: object, validator: Callable[[object], object] | None, label: str
    ) -> object:
        if validator is None:
            return payload
        try:
            validator(payload)
        except Exception as error:
            raise RuntimeError(f"{label} payload validation failed: {error}") from error
        # Validators are intentionally predicates.  Keep the serialized
        # payload unchanged so callers receive exactly what was published.
        return payload

    def load(
        self,
        inputs: Mapping[str, object],
        *,
        validator: Callable[[object], object] | None = None,
    ) -> CheckpointResult | None:
        checked_inputs = _validate_identity(inputs)
        operation = checked_inputs.get("operation")
        if not isinstance(operation, str):
            raise ValueError("checkpoint inputs have no operation")
        key = self.key_for(checked_inputs)
        path = self.path_for(key, operation)
        if not path.exists() and not path.is_symlink():
            return None
        try:
            if path.is_symlink() or not path.is_file():
                raise RuntimeError("cache entry is not a regular file")
            envelope = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(envelope, dict) or set(envelope) != _ENVELOPE_FIELDS:
                raise RuntimeError("cache envelope fields are invalid")
            if envelope.get("schema") != CHECKPOINT_SCHEMA:
                raise RuntimeError("cache schema is invalid")
            if envelope.get("key") != key:
                raise RuntimeError("cache key does not match inputs")
            if envelope.get("inputs") != checked_inputs:
                raise RuntimeError("cache inputs do not match requested inputs")
            if envelope.get("status") != "complete":
                raise RuntimeError("cache status is not complete")
            payload = envelope.get("payload")
            digest = envelope.get("payloadSha256")
            if not isinstance(digest, str) or digest != sha256(_canonical(payload)):
                raise RuntimeError("cache payload digest does not match")
            payload = self._validate_payload(payload, validator, "cached")
        except Exception as error:
            self._diagnostic(f"invalid {path}: {error}; regenerating")
            return None
        return CheckpointResult(payload, True, key)

    def _publish(self, inputs: Mapping[str, object], key: str, payload: object) -> None:
        operation = inputs["operation"]
        if not isinstance(operation, str):
            raise ValueError("checkpoint inputs have no operation")
        path = self.path_for(key, operation)
        path.parent.mkdir(parents=True, exist_ok=True)
        envelope = {
            "schema": CHECKPOINT_SCHEMA,
            "key": key,
            "inputs": dict(inputs),
            "status": "complete",
            "payloadSha256": sha256(_canonical(payload)),
            "payload": payload,
        }
        encoded = json.dumps(
            envelope, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False
        ) + "\n"
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{key}.", suffix=".tmp", dir=str(path.parent)
        )
        temporary = Path(temporary_name)
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
                stream.write(encoded)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, path)
            try:
                directory_descriptor = os.open(path.parent, os.O_RDONLY)
            except OSError:
                pass
            else:
                try:
                    os.fsync(directory_descriptor)
                finally:
                    os.close(directory_descriptor)
        finally:
            if temporary.exists():
                temporary.unlink()

    def get_or_compute(
        self,
        operation: str,
        modules: Sequence[str],
        source_hashes: Mapping[str, str] | Sequence[str],
        producer: Callable[[], object],
        *,
        parameters: Mapping[str, object] | None = None,
        validator: Callable[[object], object] | None = None,
        freshness: Callable[[], object] | None = None,
    ) -> CheckpointResult:
        inputs = self.inputs(operation, modules, source_hashes, parameters=parameters)
        cached = self.load(inputs, validator=validator)
        if cached is not None:
            return cached
        try:
            payload = producer()
            # A long-running producer may observe a source or implementation
            # edit after its key was formed.  Do not publish that result under
            # the old immutable identity; the caller's check is deliberately
            # run before validation and atomic publication.
            if freshness is not None:
                freshness()
            payload = self._validate_payload(payload, validator, "produced")
            # Ensure serialization happens before publication.  A producer that
            # returns an unserializable object is a failed batch and leaves no
            # reusable entry behind.
            _canonical(payload)
            key = self.key_for(inputs)
            self._publish(inputs, key, payload)
        except Exception:
            # _publish cleans its own temporary file; producer failures never
            # create a completed envelope.
            raise
        return CheckpointResult(payload, False, key)


__all__ = ["CHECKPOINT_SCHEMA", "CheckpointResult", "CheckpointStore", "sha256"]
