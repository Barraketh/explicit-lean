-- A user-defined macro.
set_option autoImplicit false

macro "twice " x:term : term => `($x + $x)
