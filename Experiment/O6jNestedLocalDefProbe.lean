import ExplicitLean.SimpExplicit

opaque o6jWrap : Nat → Nat
opaque o6jPayload : Nat
axiom o6jWrap_payload : o6jWrap o6jPayload = 7

set_option explicitLean.simpExplicit.report true in
example : o6jWrap o6jPayload = 7 := by
  let s := o6jPayload
  change o6jWrap s = 7
  simp_explicit? [s, o6jWrap_payload]

example : o6jWrap o6jPayload = 7 := by
  let s := o6jPayload
  let other := o6jPayload
  change o6jWrap s = 7
  fail_if_success simp_explicit [o6jWrap_payload, eq_self]
  fail_if_success
    simp_explicit [reduce local_def other, o6jWrap_payload, eq_self]
  fail_if_success
    simp_explicit [o6jWrap_payload, reduce local_def s, eq_self]
  simp_explicit [reduce local_def s, o6jWrap_payload, eq_self]
