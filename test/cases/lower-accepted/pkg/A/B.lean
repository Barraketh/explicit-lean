-- Every declaration form and context command v0 accepts, in one module. This is
-- the positive counterpart to the admit-* rejection cases: admission must
-- accept all of it, and must keep accepting it as rejection rules are added.
set_option autoImplicit false

universe u

namespace Sample

def plain : Nat := 1

abbrev alias : Nat := plain

opaque hidden : Nat

theorem plainEqOne : plain = 1 := rfl

def polymorphic (a : Type u) (x : a) : a := x

def withImplicit {a : Type u} (x : a) : a := x

def withInstance {a : Type u} [Inhabited a] (_ : a) : a := default

def withStrict {{a : Type u}} (x : a) : a := x

def usesLambda : Nat → Nat := fun n => n

def usesLet : Nat :=
  let doubled := plain
  doubled

def usesArrow : Nat → Nat → Nat := fun a _ => a

section
variable (k : Nat)

def withSectionVariable : Nat := k

end

end Sample

open Sample in
def usesOpen : Nat := plain
