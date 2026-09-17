module
prelude

public meta import ExplicitLean.ExplicitRw.Tactic

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

namespace Impl

/- Register against this syntax kind, rather than the general `term` category:
   ordinary terms must continue through Lean's existing elaborator table. -/
@[term_elab explicitRwLocalRefTerm]
public meta def elabIndexedLocal : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  elabIndexedLocalCore stx expectedType?

end Impl
end ExplicitLean.ExplicitRw
