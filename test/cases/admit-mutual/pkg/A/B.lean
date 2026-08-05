-- A mutual block.
set_option autoImplicit false

mutual
  def isEven : Nat → Bool
    | 0 => true
    | (n + 1) => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | (n + 1) => isEven n
end
