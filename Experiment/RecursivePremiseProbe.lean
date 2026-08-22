import ExplicitLean.SimpExplicit

opaque RecursiveP : Prop
opaque RecursiveQ : Prop
opaque recursiveNat : Nat := 0

axiom recursiveQToTrue : RecursiveQ = True
axiom recursivePToTrue (h : RecursiveQ) : RecursiveP = True
axiom recursiveOuter (h : RecursiveP) :
  recursiveNat + 0 = recursiveNat

set_option explicitLean.simpExplicit.report true in
example : recursiveNat + 0 = recursiveNat := by
  simp_explicit? only [recursiveOuter, recursivePToTrue, recursiveQToTrue, eq_self]
