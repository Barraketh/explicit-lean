-- Imported instance synthesis: the source writes an overloaded operation and
-- elaboration selects a dictionary the source never names.
set_option autoImplicit false

def addNats (a b : Nat) : Nat := a + b

def mulNats (a b : Nat) : Nat := a * b

-- `HAdd.hAdd` and its `instHAdd`/`instAddNat` dictionary are chosen by instance
-- search, so capture must recover them from the completed value.
def sum : Nat := addNats 2 3

def eqTest (a b : Nat) : Bool := a == b
