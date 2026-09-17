# T9: authenticated source-site identity

> Superseded by the user's non-adversarial-environment direction on
> 2026-09-17. Keep the site-bijection diagnosis and source-range/call-text
> mapping, but hashes, nonces, byte authentication and forgery tests are not
> implementation requirements. The current contract is
> `tracking/SIMP-TRACE-SPEC.md`.

## Finding

The T4 review-4 failure is a producer/consumer contract failure, not a Lean
replay failure.  T1's `test/SimpTrace/make_traced.py` and
`test/SimpTrace/check_transcription.py` skip an entire source line when it
contains `@[`:

```python
if "@[" in line or stripped.startswith("attribute"):
    ...                 # do not scan the line
```

That makes the old T1 count silently omit executable tactics on declaration
lines carrying an attribute.  T4's `sites.mask_attributes` blanks only the
attribute span and then scans the rest of the line, so it correctly finds the
two calls in the pinned source:

```text
Mathlib/Logic/Function/Basic.lean:698  @[simp] lemma update_eq_self_iff ... := by simp [update_eq_iff]
Mathlib/Logic/Function/Basic.lean:700  @[simp] lemma eq_update_self_iff ... := by simp [eqComm]
```

The first nine sites agree.  T4's Python `Site.start/end` reports the call
`simp [update_eq_iff]` at character range `[27074,27094)` (the corresponding
UTF-8 byte range is `[29177,29197)`); T1 has no corresponding trace and T4 consumes
`FunctionBasicTraced_10.json`, which is actually the later call `simp [*]` at
source line 797 (the `Pi.map` declaration).  T4 site 11 similarly consumes
trace 11 for the later `extend_def` call.  Every subsequent numeric pairing is
shifted by two.  The T1 files confirm the cause: the traced copy still contains
the original `@[simp] ... := by simp ...` text at lines 699 and 701, while its
trace filenames stop at 23.  `check_transcription.py` passes only because its
`@[` line skip repeats the same blind spot.

The current trace JSON has exactly these top-level keys:
`schema`, `module`, `occurrence`, `call`, `locations`.  `module` is the
generated name `test.SimpTrace.FunctionBasicTraced`, `occurrence` is the
decimal `getRef` position from the instrumented copy, and `call` is the
transformed syntax, for example
`"simp_trace [*] =>trace \"..._10.json\""`.  There is no `range`, source
filename, call hash, source hash, site ordinal, or authenticated invocation
identity.  `occurrence` is therefore diagnostic only: instrumentation changes
its coordinate, and it is not an identity in the original source.

No module result from the current harness is acceptance evidence.  T1 must
trace both sites, but that is necessary rather than sufficient: a module is
accepted only after the complete authenticated source-site bijection below
passes.

## Contract

Add a producer-side site manifest to each traced copy and an identity envelope
to every emitted trace.  This is a protocol revision (use `simp-trace-v2` or a
separate `identitySchema: 1`; do not silently interpret v1 as authenticated).
All offsets are end-exclusive UTF-8 byte offsets in the exact original source
bytes.  Character offsets are Unicode scalar/code-point offsets, not display
columns.

The manifest is canonical JSON (UTF-8, sorted object keys, no insignificant
whitespace) and has the following fields:

```json
{
  "identitySchema": 1,
  "modulePath": "Mathlib/Logic/Function/Basic.lean",
  "sourceSha256": "<sha256 of original source UTF-8 bytes>",
  "sourceBytes": 52979,
  "sites": [
    {
      "siteOrdinal": 9,
      "startByte": 29177, "endByte": 29197,
      "startChar": 27074, "endChar": 27094,
      "line": 698, "column": 68,
      "callText": "simp [update_eq_iff]",
      "callSha256": "<sha256 of callText UTF-8 bytes>"
    }
  ]
}
```

`siteOrdinal` is zero-based source order and is only a diagnostic/indexing
field.  `startByte`, `endByte`, and `callSha256` together identify the call;
the consumer must also compare the exact `callText` slice.  `line` and
`column` are diagnostics and must never be used for matching.  For non-ASCII
source, `startChar`/`endChar` provide a cross-check, not a replacement for
byte ranges.  The manifest records all executable simp-family calls, including
two calls on one line and calls after an attribute span; attributes themselves
are not sites.

Each trace must contain this envelope (the existing locations/steps remain
inside it):

```json
{
  "schema": "simp-trace-v2",
  "modulePath": "Mathlib/Logic/Function/Basic.lean",
  "sourceSha256": "<same manifest hash>",
  "manifestSha256": "<sha256 of canonical manifest>",
  "site": {
    "siteOrdinal": 9,
    "startByte": 29177, "endByte": 29197,
    "startChar": 27074, "endChar": 27094,
    "callText": "simp [update_eq_iff]",
    "callSha256": "<same call hash>"
  },
  "occurrence": "<getRef position in generated traced copy>",
  "tracedSourceSha256": "<sha256 of generated traced-copy bytes>",
  "tracedRange": {"startByte": 32092, "endByte": 32108},
  "invocation": 0,
  "invocations": 1,
  "locations": []
}
```

`modulePath`, source hash, manifest hash, site range, exact call slice, and call
hash are authenticated identity.  `occurrence`, `tracedSourceSha256`, and
`tracedRange` are retained for diagnostics and provenance; they are not used
to map a trace.  The trace's `callText` is the original `simp`/`simp only` text,
not the generated `simp_trace` syntax.  If retaining generated syntax is
useful, call it `tracedCall` and never overload `call`.

For a site executed more than once, all records carry the same site identity.
`invocation` is a zero-based ordinal and `invocations` is the common total.
The consumer requires exactly one record for every ordinal in
`0 .. invocations-1`; identical JSON or identical step content is still a
duplicate, never a reason to deduplicate.  A single invocation uses
`invocation: 0, invocations: 1` rather than omitted fields.  A run identifier
and fresh trace-output nonce should also be present in the envelope or manifest
so stale outputs cannot be mistaken for the current compile.

The producer must derive the manifest from the uninstrumented original bytes,
then generate the traced copy from that manifest.  It must not reconstruct
identity from the instrumented `getRef` position.  The generator must fail if
any manifest site was not replaced exactly once, if any executable source site
was not in the manifest, or if any generated trace lacks the corresponding
manifest identity.  This specifically fixes both `@[simp]` lines rather than
weakening the detector.  The traced copy may add imports, comments, trace
clauses, or otherwise change offsets; those edits only affect provenance
fields and cannot change the original identity.

## Consumer validation and reporting

T4 validates the complete source and trace set before calling `render_site`,
`render_trace`, or writing a translated module.  It computes the source hash,
rebuilds the same site manifest, verifies the manifest hash, then checks every
trace envelope.  Matching is by `(modulePath, sourceSha256, site range,
callText, callSha256)`, with `siteOrdinal` as a consistency check.  A stale
generated copy, changed source offsets, generated-module name, or altered
`occurrence` cannot pass as a match.

The validation result must be machine-readable and must contain counts and
full identity lists:

```json
{
  "identity": "rejected",
  "expectedSites": 25,
  "observedTraceRecords": 23,
  "missingSites": [{"siteOrdinal": 9, "line": 698, "callText": "..."}],
  "extraTraces": [],
  "duplicateSiteInvocations": [],
  "invalidRecords": [],
  "renderAttempted": false
}
```

Report separate categories for missing sites, extra/unmatched traces,
duplicate site/invocation keys, malformed fields, source/manifest hash
mismatch, and incomplete invocation ordinals.  Never shift numeric slots,
guess by line, choose the nearest call, or render a subset after any category
fails.  `renderAttempted` must remain false.  The module status is a single
fail-closed `identity_failed` result; it contributes zero replayed sites.

## Regression fixtures and commands

The fixture source must contain all of the following in one small module:

1. Two same-line declaration attributes followed by executable calls, exactly
   the `update_eq_self_iff` and `eq_update_self_iff` shape at lines 698/700.
2. Two executable calls on one line (`by simp [p]; simp [q]`), with distinct
   ranges and ordinals.
3. Two text-identical calls at different ranges; both must remain separate.
4. One site with two invocation records (`0/2`, `1/2`), including identical
   step payloads; missing, duplicate, and out-of-range ordinals must reject.
5. A generated copy with a long injected header and Unicode before the calls;
   original ranges and hashes must still authenticate.

After implementation, run from the T1 worktree:

```sh
python3 -B test/SimpTrace/make_traced.py Logic/Function/Basic.lean FunctionBasicTraced
python3 -B test/SimpTrace/check_transcription.py
lake env lean test/SimpTrace/FunctionBasicTraced.lean
python3 -B Experiment/check_simp_trace.py
```

The transcription check must report 25 source sites and 25 converted sites
for Function/Basic, and must inspect exact manifest ranges rather than only
counting `simp_trace` tokens.  From the T4 worktree, the authenticated gate
and the real module check are:

```sh
python3 -B Experiment/pipeline/check_pipeline.py
python3 -B Experiment/pipeline/replay_module.py \
  --module Mathlib/Logic/Function/Basic.lean \
  --t1 /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture \
  --t2 /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw \
  --out /tmp/t4-site-identity
```

The Python fixture suite must forge, independently, a missing site, an extra
trace, a duplicate `(siteOrdinal, invocation)`, a wrong call hash, a wrong
source hash, and a stale traced-copy offset.  Each case must assert rejection
and `renderAttempted == false`.  The final six-module harness must show an
identity-authenticated 84-site denominator before any replay count is
reported; the 91-site cone is held until the same gate passes.
