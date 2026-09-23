# T77 `missing_source_application`

## Result

Implemented a narrow, principled correction to source-application binder
inspection in `ExplicitLean/SimpTrace/Recorder.lean`. `hasExplicitSourceHole`
now reduces each inferred function type using ordinary (`.default`)
transparency before inspecting its actual Π binder. This lets the checker
recognize explicit arguments hidden behind definitional membership wrappers;
it does not identify arguments by spelling, declaration name, or source path,
and does not serialize proof terms.

The exact fresh reproduction was the staged pending-worker source for
`Mathlib.RepresentationTheory.Invariants.add_mem'`, whose source arguments
include `hv g`, `hw g`, and `map_add`. Before the change, the type of an
application remained a partially applied `Membership.mem` projection and the
checker conservatively classified it as an uninspectable explicit hole. With
ordinary transparency, the Π binder is exposed and the source rewrite trace is
accepted.

The correction leaves the explicit-hole and binder-identity rules intact:
metavariables in explicit binders remain rejected; implicit and
instance-implicit metavariables retain their existing treatment; inference or
WHNF failures and non-Π application types still fail closed; source ranges,
`argId`, malformed-evidence validation, and multi-theorem source-argument
handling are unchanged.

## Evidence

Checks run from this isolated worktree:

- `lake build ExplicitLean.SimpTrace` — passed.
- Fresh reproduction of the staged `Mathlib.RepresentationTheory.Invariants`
  source — passed after the change; it previously reported
  `missing_source_application`.
- `python3 -B test/SimpTrace/check_missing_source_application.py` — passed
  applied local hypotheses, membership-wrapped application, choice property,
  subtype property, `show ... from ...`, authenticated source range/argument
  identity, the exact `Representation.Invariants.add_mem'` source shape (both
  `hv g` and `hw g` resolve as source arguments 0 and 1), and the case where
  one source argument yields multiple simp theorems. The direct adversarial
  checks cover a semireducible Π alias, an explicit metavariable nested under
  a definition, an allowed implicit metavariable, unresolved and opaque
  function types that fail closed, and preservation of all tested
  metavariable assignments.
- `python3 -B test/SimpTrace/check_source_applied_arguments.py` — passed,
  including rejection of a bare source theorem when its required proof-side
  evidence is absent.
- `python3 -B test/SimpTrace/check_t77_nezero_source_evidence.py` — passed,
  including mismatched source proposition and unrelated-source controls.
- `python3 -B -m py_compile test/SimpTrace/check_missing_source_application.py`
  and `git diff --check` — passed.

No full campaign, simp-disabled certification, or simp-family output run was
performed. No database, live worker state, or campaign tracker was edited by
this task.

## Review note

Independent trust-boundary review confirmed that `.default` WHNF only exposes
the actual Π binder needed to classify each application argument. Explicit
holes remain rejected through semireducible wrappers and nested applications;
opaque or still-uninspectable function types fail closed. The review added a
`withoutModifyingMCtx` boundary around the predicate so WHNF/type inference
cannot persist metavariable or cache changes to the source elaboration or
matcher. The direct tests assert that both allowed and rejected metavariables
remain unassigned after validation. Focused suites pass.

During initial diagnosis, one fresh compiler reproduction used a copied staged
Lean file whose embedded trace output path pointed into the live pending-run
scratch tree. A subsequent read-only audit found only the pre-existing raw
trace at that path (mtime `2026-09-23T05:20:06-0400`, SHA-256
`8dfc098bc0c831d12deb2fc7a5dc7cbc69c36e1e8a99de7be6b7f9a32ff3696d`), with no
new sibling. No matching reproduction process remains. All later tests used
fresh output paths under this isolated worktree's `.lake/private` directory.
