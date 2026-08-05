-- A class declaration and an instance registration.
set_option autoImplicit false

class Default (a : Type) where
  value : a

instance : Default Nat where
  value := 0
