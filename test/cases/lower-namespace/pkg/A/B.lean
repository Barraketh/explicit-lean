-- Namespace, section, variable, and open commands: context that shapes name
-- resolution and declaration headers without itself producing constants.
set_option autoImplicit false

namespace Outer

def base : Nat := 7

namespace Inner

def usesBase : Nat := base

end Inner

section
variable (k : Nat)

-- `k` is a section variable, so the elaborated declaration has a parameter the
-- body's syntax never binds.
def withSectionVar : Nat := k + base

end

end Outer

open Outer in
def usesOpen : Nat := base
