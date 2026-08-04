-- A source elaboration failure is exit status 3, and capture must not leak the
-- compiler's own names into the source environment.
set_option autoImplicit false

def usesCompilerName : Nat := ExplicitLean.captureArchitecture
