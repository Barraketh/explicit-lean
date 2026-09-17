# T22 direct source-argument identity

Status: implemented on `task/T22-source-arg-ids`.

The recorder registers site-local argument IDs and canonical source spans from
the parser syntax before stock `mkSimpContext` runs.  `Origin.stx` entries are
joined to that side table by their exact range, so preprocessing and
one-to-many rules retain one direct `argId`; direction and term-free
head/local metadata are captured at registration.  The v1 raw trace emits
`sourceArgs` and rule derivations use `argId`; the source manifest carries the
same spans and validates their exact source slices before v2 finalization; the
v2 site carries those `sourceArgs` records forward.

Parser byte positions are retained only in-memory for the `Origin.stx` join.
The serialized `startChar`/`endChar` values are converted by walking the exact
UTF-8 file-map source and are Unicode-scalar offsets.  The reverse fixture has
both a UTF-8 comment before the call and a UTF-8 `←` inside the argument; its
fresh capture is checked by `check_t22_source_args.py` against direct source
slices.

Fresh `T22SourceArgIdentity.lean` covers conditional lambda, field/local
argument, named implicit argument, reverse application, conjunction
one-to-many projection, repeated text, and wildcard/inaccessible context.

Checks:

* `lake build ExplicitLean.SimpTrace` — pass.
* `lake env lean test/SimpTrace/Fixtures.lean` — pass (existing linter warning).
* `lake env lean test/SimpTrace/T22SourceArgIdentity.lean` — pass.
* `python3 -B test/SimpTrace/check_t22_source_args.py` — pass (fresh UTF-8
  scalar slices, reverse direction, repeated IDs, and one-to-many IDs).
* `python3 -B test/SimpTrace/test_trace_identity.py` — 22 tests pass.
* Campaign supervisor/worker and translation-index checks — pass.
* `python3 -B Experiment/check_simp_trace.py --allow-suffixed-invocations` —
  pass; 81 canonical skeletons checked and each known suffixed recorder
  invocation structurally validated against its canonical skeleton before it
  is explicitly allowed.  Seven canonical T22 skeletons are committed.
* `python3 -B test/SimpTrace/check_suffixed_traces.py` — pass; a valid known
  `chained.1.json` succeeds, a forged `kind: "bogus"` suffix fails, and an
  unknown suffix fails.
* `git diff --check` — pass.

No renderer, ExplicitRw, theorem-table ordinal attribution, callText parsing,
proof serialization, hash, nonce, or reconstruction was added.
