# T59 escalation: commutativity simprocs

The unconditional `Simp.Step.continue` swap is not equivalent to stock
`withoutTheorems`. With that replacement enabled, the pinned compiler fails at
`Mathlib.Logic.Function.Basic.eq_update_self_iff`:

```lean
@[simp] lemma eq_update_self_iff : f = update f a b ↔ f a = b := by simp [eqComm]
```

The swapped function equality is revisited until maximum recursion depth. Stock
prevents this by simplifying under an exact lexical exclusion set before it
returns a result.

The replacement is withheld. A future solution must preserve the exclusion
context and pass the dependent probe; certification or a small direct fixture
alone is insufficient.
