-- Coercion insertion: the source writes a value of one type where another is
-- expected and elaboration inserts the coercion.
set_option autoImplicit false

def asInt (n : Nat) : Int := n

def literalInt : Int := 5

def viaCoe (n : Nat) : Int := asInt n + 1
