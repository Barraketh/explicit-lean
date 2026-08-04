-- Universe-polymorphic declarations, explicit universe declarations, and the
-- universe arguments elaboration inserts at each use site.
set_option autoImplicit false

universe u v

def idAt (α : Type u) (a : α) : α := a

def constAt (α : Type u) (β : Type v) (a : α) (_ : β) : α := a

-- `idAt` is used here at a universe the source never writes down, so capture
-- must recover the inserted universe argument.
def usesId : Nat := idAt Nat 3

def usesConst (α : Type u) (a : α) : α := constAt α Nat a 0
