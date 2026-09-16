# Personal review: stock simp and active boundary replay

Reviewed by the primary coordinator at the user's explicit request. No Luna
transcripts were read and no review implementation was delegated. Local HEAD:
`2d611711ba0374e47669a8ddf7d8a37473330caf`; Lean `v4.32.2`.

## Conclusion

The active architecture records checked results, proofs and persistent effects;
it does not need to duplicate the simplifier's search algorithm. This is a sound
design direction, but the implementation does not yet cover every stock `simp`
boundary. One semantic mismatch was reproduced. Two explicit codec limitations
also reject valid classes of effects. No accepted incorrect theorem was found;
this review is not a proof of complete equivalence or an exhaustive audit.

The active path is `Boundary.lean`, `Boundary/Apply.lean` and
`Boundary/Tactic.lean`, generating `simp_engine_boundary_select`. The older
schema-27 `Replay.lean` / `simp_engine_apply` is not the campaign engine.

## Confirmed bug: hypothesis processing changes the instance context too early

`Boundary.lean:2348–2381`, particularly `current.withContext` at line 2361,
does not match pinned Lean's `Meta/Tactic/Simp/Main.lean:874–911`.

Stock `simpGoal` simplifies all selected hypotheses under the original goal's
outer `withContext`. Proof-free replacements update the goal being constructed,
but the next hypothesis is still simplified under the original reader context.
The recorder instead re-enters the updated goal context for each hypothesis.

This matters because `replaceLocalDeclDefEq` registers newly exposed class
instances (`Meta/Tactic/Replace.lean:110–132`). Unfolding an ordinary definition
to a class in the first hypothesis can therefore enable a conditional rewrite
of the second hypothesis in recording, while stock `simp` leaves it unchanged.

Reproducer:

```lean
import ExplicitLean.SimpEngine.Boundary
class ReviewC : Prop where
  h : True
def ReviewHiddenC : Prop := ReviewC
inductive ReviewBox : Prop where | intro
theorem review_box [ReviewC] : ReviewBox ↔ True :=
  ⟨fun _ => .intro, fun _ => .intro⟩
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp only [ReviewHiddenC, review_box] at h k
  exact k
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp_engine_boundary_probe only [ReviewHiddenC, review_box] at h k
  exact k
```

The stock example compiles. The probe fails with
`boundary_comparison_mismatch:goals[0].locals[2].fvar.injective`.
This is a coverage failure detected by the existing comparison, not evidence
that a false theorem is accepted.

Fix direction: retain the original goal reader context for the entire local
simplification loop, matching stock; use the updated goal context when stock
does, including target simplification. Preserve comparison and reference guards.
Add this regression, then check dependent hypotheses, conditional rewrites,
proof-free and proof-bearing changes, target processing and encoded replay.
Do not simply remove context switching everywhere: replacement helpers and
target simplification have their own stock context behavior.

## Explicit coverage limitations, not demonstrated silent semantic bugs

* `Boundary/SequenceCodec.lean:134–141` rejects more than one helper in its
  imported mixed cached/fresh realization branch. The local sequence codec is
  separate and already supports additional cases. The imported branch places
  registrations before the sole helper (`:202–224`); merely removing the size
  guard would be incorrect because multiple helpers can observe different
  environment snapshots. A generalization must represent that ordering.
* `Boundary/RealizationCodec.lean:123–129` requires an empty auxiliary proof
  cache in the bounded member-metadata contract. Imported completed-cache
  descriptors call this contract (`:196–224`). Valid imported realizations
  outside it fail with `activation_nonempty_aux_cache`. Separate local cached
  auxiliary support exists, so this is not a claim that all auxiliary caches
  are unsupported. Extend the authenticated cache-effect representation rather
  than bypassing the guard or rerunning simplification during replay.

These findings justify engine-level work before declaration-specific rewrites.
They do not establish how many of the historical 62 failures each fix resolves.

## Other checks and limits

* The difference in proof-free `False` closure order between stock and Apply
  did not produce a mismatch in the focused alias-to-False fixture.
* A conjunction theorem producing simplifier helpers passed a focused probe.
  The earlier allocator suspicion remains unconfirmed. The allocator advances
  on name conflicts, not unconditionally on every allocation; this test is not
  an exhaustive name-generation test.
* `Boundary/Tactic.lean:252–268` checks explicit equality proofs, but has no
  corresponding input/result definitional-equality check when proof is absent.
  This is a candidate decoder hardening task, not a demonstrated kernel
  unsoundness. Any added check must respect transparency and state guards.
* Lean compilation checks resulting declarations. It does not, by itself,
  establish identical goal contexts, instance availability, environment caches,
  names or computational behavior. Keep boundary and declaration comparisons.

## Reproducible evidence

Three isolated fixtures ran on the already authorized AWS host at pinned HEAD
`5145cfbff9ba1b2e99648c04691f8b92265f41a3`. The script verified a clean remote
checkout and hashes of the relevant engine sources. It wrote only a fresh
`/tmp/explicit-lean-review-1y5oz_i3` directory. Each Lean process was restricted
to one core, low priority, 8 GiB virtual memory, 40 CPU seconds and 55 wall
seconds, with a fresh 20 GiB available-memory guard.

SSM command: `94b03f3f-7a73-4d90-8e5d-3aa64b6bd254`, Success/0 for the driver.
Individual results: FalseClosure exit 0 (0.67s), HelperAllocation exit 0 (0.74s),
LocalContext exit 1 (0.65s), with the expected mismatch above. Driver success
does not mean all fixtures passed.

Local sources, driver and raw SSM receipt:
`.lake/replay-review-405c8875f1844820a130be93dd971cde/`.
Receipt `ssm-result.json` SHA256:
`451d6233a2e62851b8588a96daab898b9184c9454475bf1b10c07ade96df90e2`.
These are focused probe results, not encoded-roundtrip, module, or whole-tree
acceptance. The active cloud verifier was not restarted or modified. No engine
source was changed during this review.

## Next work, in order

1. Fix the confirmed local-context bug and run focused stock/capture/encoded
   replay regression checks before committing implementation.
2. Independently specify imported multi-helper ordering and imported auxiliary
   cache effects, then implement and review those bounded extensions.
3. Investigate allocator failures using an isolated reproducer before changing
   name-generation contracts. Consider proof-free decoder validation separately.
4. Retry affected manifest entries provisionally, retaining final authenticated
   manifest, declaration comparisons and whole-tree acceptance requirements.

The current authorized pilot and its immutable cutoff remain unchanged. This
review does not authorize another host, worker dispatch or campaign extension.

## Fix completion, September 16

The confirmed context mismatch is fixed in `f6a5086`, with encoded replay
regressions in `4ae57bf`. Ordered imported multi-helper support is committed in
`e813e53`; authenticated imported auxiliary-cache support is in `a407a01`.
Local and imported auxiliary caches now use one proof/cache validation worker,
with separate adapters for their descriptor formats. Both paths remain active;
"local" means declarations in the current Lean module, not a machine-local
alternative engine.

The isolated AWS shared build, original context probe, encoded context replay,
multi-helper controls, imported auxiliary runtime and six wire-mutation controls,
and existing mixed/local-auxiliary/realization-group suites pass. Exact commands,
source hashes and report hashes are recorded in `campaign.json`. The initial
24 GiB virtual-memory cap caused allocation failures even on the unchanged
baseline; the unchanged checks passed at 64 GiB. The auxiliary run peaked at
12,599,660 KiB resident and 31,163,124 KiB virtual memory.

The imported auxiliary fixture authenticates an existing completed imported
cache with controlled auxiliary entries. It does not establish fresh
producer-side reconstruction or acceptance of the original failing Mathlib
modules. Those module retries, declaration comparisons and whole-tree acceptance
remain subsequent work. No campaign coverage count advanced, and the sole
authorized pilot and its cutoff were unchanged.
