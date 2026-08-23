import ExplicitLean.SimpExplicit

/-! A projection function whose major argument becomes a constructor only
    after head-beta reduction. Closed replay keeps ambient beta/projection
    reduction disabled; the named projection command enables both operations
    only inside the pinned projection-function reducer. -/

structure O6gProjectionRecord where
  value : Nat

structure O6gOtherProjection where
  value : Nat

opaque o6gPayload : Nat → Nat

@[simp] axiom o6gPayload_eq (n : Nat) : o6gPayload n = n

example (n : Nat) :
    O6gProjectionRecord.value ((fun x => { value := o6gPayload x }) n) = n := by
  simp_explicit [reduce projection_fn O6gProjectionRecord.value, o6gPayload_eq]

set_option explicitLean.simpExplicit.report true in
example (n : Nat) :
    O6gProjectionRecord.value ((fun x => { value := o6gPayload x }) n) = n := by
  simp_explicit?

example (n : Nat) :
    O6gProjectionRecord.value ((fun x => { value := o6gPayload x }) n) = n := by
  fail_if_success
    simp_explicit [reduce projection_fn O6gOtherProjection.value, o6gPayload_eq]
  change o6gPayload n = n
  exact o6gPayload_eq n
