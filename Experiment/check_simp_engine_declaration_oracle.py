#!/usr/bin/env python3
"""Exercise the declaration/environment oracle on bounded source pairs.

Each pair uses the same module identity and filename, so private names are
stable while the stock and applied sources live in separate temporary roots.
The accepted cases document the semantic equivalences the oracle permits; the
rejected cases make sure a changed observable declaration or environment is
fail-closed.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
ORACLE = "Experiment/SimpEngineDeclarationOracle.lean"
MARKER = "SIMP_ENGINE_DECLARATION_ORACLE "
KIND = "simp_engine_declaration_oracle"
SCHEMA = 1
TIMEOUT = 600


@dataclass(frozen=True)
class Case:
    name: str
    stock: str
    applied: str
    accepted: bool
    category: str | None = None
    private_proof_counts: tuple[int, int, int] | None = None
    detail_contains: str | None = None


def source(body: str) -> str:
    return "module\n\nimport Mathlib\n\npublic section\n\n" + body + "\n"


CASES = (
    Case(
        "proof-body-difference",
        source("theorem oracleSample : True := by trivial"),
        source("theorem oracleSample : True := by exact True.intro"),
        True,
    ),
    Case(
        "module-doc-range-shift",
        source("/-! Oracle module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        "module\n\nimport Mathlib\n"
        "import ExplicitLean.SimpEngine.Boundary.Tactic\n\n"
        "public section\n\n/-! Oracle module documentation. -/\n\n"
        "theorem oracleSample : True := True.intro\n",
        True,
    ),
    Case(
        "module-doc-text-mismatch",
        source("/-! Stock module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        source("/-! Applied module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "derived-module-use-subset",
        source(
            "run_cmd Lean.recordExtraModUse `Mathlib.Data.Int.Cast.Basic false\n"
            "theorem oracleSample : True := True.intro"
        ),
        source("theorem oracleSample : True := True.intro"),
        True,
    ),
    Case(
        "added-module-use",
        source("theorem oracleSample : True := True.intro"),
        source(
            "run_cmd Lean.recordExtraModUse `Mathlib.Data.Int.Cast.Basic false\n"
            "theorem oracleSample : True := True.intro"
        ),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "axiom-subset-mismatch",
        source("theorem oracleSample : True := True.intro"),
        source("theorem oracleSample : True := Classical.choice ⟨True.intro⟩"),
        False,
        "axiom_subset_mismatch",
    ),
    Case(
        "defeq-computational-difference",
        source("def oracleSample : Nat := Nat.succ 0"),
        source("def oracleSample : Nat := 1"),
        True,
    ),
    Case(
        "non-defeq-data",
        source("def oracleSample : Nat := 1"),
        source("def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "type-mismatch",
        source("def oracleSample : Nat := 1"),
        source("def oracleSample : Int := 1"),
        False,
        "declaration_type_mismatch",
    ),
    Case(
        "opaque-non-proof-mismatch",
        source("opaque oracleSample : Nat := 1"),
        source("opaque oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "irreducible-non-proof-mismatch",
        source("@[irreducible] def oracleSample : Nat := 1"),
        source("@[irreducible] def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "unsafe-runtime-mismatch",
        source("unsafe def oracleSample : Nat := 1"),
        source("unsafe def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "public-attribute-mismatch",
        source("theorem oracleSample : (1 : Nat) = 1 := rfl"),
        source(
            "theorem oracleSample : (1 : Nat) = 1 := rfl\n"
            "attribute [simp] oracleSample"
        ),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "private-proof-helper-omission",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source("theorem oracleSample : True := True.intro"),
        True,
    ),
    Case(
        "private-proof-helper-metadata-difference",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private opaque oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        True,
        private_proof_counts=(0, 0, 2),
    ),
    Case(
        "private-proof-helper-type-difference",
        source(
            "private theorem oracleWarmup : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private theorem oracleWarmup : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "private theorem oraclePrivateHelper : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "theorem oracleSample : True := True.intro"
        ),
        True,
        private_proof_counts=(0, 0, 3),
    ),
    Case(
        "private-proof-classification-mismatch",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private def oraclePrivateHelper : Nat := 1\n"
            "theorem oracleSample : True := True.intro"
        ),
        False,
        "declaration_set_mismatch",
        detail_contains="private-proof classification differs",
    ),
    Case(
        "private-computational-omission",
        source(
            "private def oraclePrivateHelper : Nat := 1\n"
            "theorem oracleSample : True := True.intro"
        ),
        source("theorem oracleSample : True := True.intro"),
        False,
        "declaration_set_mismatch",
    ),
    Case(
        "added-axiom",
        source("theorem oracleSample : True := True.intro"),
        source(
            "axiom oracleAddedAxiom : False\n"
            "theorem oracleSample : True := oracleAddedAxiom.elim"
        ),
        False,
        "declaration_set_mismatch",
    ),
)


def run(command: list[str], timeout: int = TIMEOUT) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"command failed ({completed.returncode}): {command}\n{completed.stdout}")
    return completed.stdout


def build_library() -> str:
    run(["lake", "build", "ExplicitLean:shared"])
    output = run(["lake", "query", "ExplicitLean:shared", "--json"])
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    try:
        path = json.loads(lines[-1])
    except (IndexError, json.JSONDecodeError) as error:
        raise RuntimeError("lake query ExplicitLean:shared returned invalid JSON") from error
    if not isinstance(path, str) or not path:
        raise RuntimeError(f"lake query ExplicitLean:shared returned invalid path: {path!r}")
    return path


def parse_report(output: str) -> dict[str, object]:
    reports = [
        json.loads(line.split(MARKER, 1)[1].strip())
        for line in output.splitlines()
        if line.startswith(MARKER)
    ]
    if len(reports) != 1 or not isinstance(reports[0], dict):
        raise RuntimeError(f"oracle emitted {len(reports)} canonical markers:\n{output}")
    report = reports[0]
    if report.get("kind") != KIND or report.get("schema") != SCHEMA:
        raise RuntimeError(f"oracle marker identity mismatch: {report}")
    return report


def check_case(case: Case, dylib: str, root: Path, ordinal: int) -> None:
    stock_dir = root / f"{ordinal:02d}-stock"
    applied_dir = root / f"{ordinal:02d}-applied"
    stock_dir.mkdir()
    applied_dir.mkdir()
    stock_path = stock_dir / "Fixture.lean"
    applied_path = applied_dir / "Fixture.lean"
    stock_path.write_text(case.stock, encoding="utf-8")
    applied_path.write_text(case.applied, encoding="utf-8")
    module = "Experiment.SimpEngine.DeclarationOracleFixture"
    command = [
        "lake",
        "env",
        "lean",
        f"--load-dynlib={dylib}",
        "--run",
        ORACLE,
        module,
        str(stock_path),
        str(applied_path),
    ]
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=TIMEOUT,
        check=False,
    )
    report = parse_report(completed.stdout)
    accepted = report.get("status") == "success" and completed.returncode == 0
    if accepted != case.accepted:
        raise RuntimeError(
            f"{case.name}: expected accepted={case.accepted}, got {report};\n"
            f"{completed.stdout}"
        )
    if case.category is not None and report.get("failureCategory") != case.category:
        raise RuntimeError(
            f"{case.name}: expected category {case.category!r}, got {report};\n"
            f"{completed.stdout}"
        )
    detail = report.get("failureDetail")
    if case.category is not None and (not isinstance(detail, str) or not detail):
        raise RuntimeError(
            f"{case.name}: expected a failure detail, got {report};\n{completed.stdout}"
        )
    if case.private_proof_counts is not None:
        actual_counts = (
            report.get("stockOnlyPrivateProofCount"),
            report.get("appliedOnlyPrivateProofCount"),
            report.get("checkedDeclarationCount"),
        )
        if actual_counts != case.private_proof_counts:
            raise RuntimeError(
                f"{case.name}: expected private-proof/accounted counts "
                f"{case.private_proof_counts}, got {actual_counts};\n{completed.stdout}"
            )
    if case.detail_contains is not None and (
        not isinstance(detail, str) or case.detail_contains not in detail
    ):
        raise RuntimeError(
            f"{case.name}: expected detail containing {case.detail_contains!r}, "
            f"got {detail!r};\n{completed.stdout}"
        )


def main() -> None:
    dylib = build_library()
    with tempfile.TemporaryDirectory(prefix="declaration-oracle-", dir=ROOT / ".lake") as raw:
        root = Path(raw)
        for ordinal, case in enumerate(CASES):
            check_case(case, dylib, root, ordinal)
    print(
        "declaration oracle: "
        f"{sum(case.accepted for case in CASES)} accepted-equivalence and "
        f"{sum(not case.accepted for case in CASES)} fail-closed cases passed"
    )


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.SubprocessError) as error:
        print(f"declaration oracle checker failed: {error}", file=sys.stderr)
        raise SystemExit(1)
