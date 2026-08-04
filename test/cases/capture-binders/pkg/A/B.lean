-- Binder styles and the arguments elaboration supplies at each use site:
-- explicit, implicit, strict-implicit, and instance binders.
set_option autoImplicit false

universe u

def explicitOnly (α : Type u) (a : α) : α := a

def withImplicit {α : Type u} (a : α) : α := a

def withStrictImplicit {{α : Type u}} (a : α) : α := a

def withInstance {α : Type u} [Inhabited α] (_ : α) : α := default

-- Each use below omits arguments the source never writes, so capture must
-- recover the implicit type, the strict-implicit type, and the dictionary.
def useImplicit : Nat := withImplicit 1

def useStrict : Nat := withStrictImplicit 2

def useInstance : Nat := withInstance 3

-- A function type written with an arrow rather than an explicit binder.
def arrowTyped : Nat → Nat := fun x => x
