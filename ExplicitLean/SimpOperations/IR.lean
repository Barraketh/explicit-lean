module
prelude

public import ExplicitLean.SimpEngine.IR

public section

namespace Lean.Meta.Simp.Operations

open Engine

/-- A rewrite operand stripped down to source-replayable identity.  In
particular, local operands carry only their stable context index: no type,
value, expression, proof, or fingerprint crosses this boundary. -/
inductive RuleOrigin where
  | decl (name : Name)
  | equation (declaration : Name) (index : Nat)
  | local (contextIndex : Nat)
  /-- Exact parser source for a rule supplied as a nontrivial `simp` operand.
  This is source syntax, not an elaborated term or proof payload. -/
  | syntax (source : String)
  | other (name : Name)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/-- A definitional operation stripped of legacy validation payloads. -/
inductive Reduction where
  | instantiateMVars
  | beta
  | projection (structureName : Name) (field : Nat)
  | projectionFunction (name : Name) (branch : ProjectionBranch)
  | iota
  | zetaUsed (zetaHave : Bool)
  | zetaUnused
  | delta (name : Name) (strategy : DeltaStrategy)
  | foldRawNatLit
  | localDef (contextIndex : Nat) (reason : LocalDefReason)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/-- The identity operands needed to reapply one already-selected rewrite rule.
No instantiated expression, proof term, fingerprint, or simp-table snapshot is
part of this source-facing record. -/
structure Rule where
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  numExtraArgs : Nat
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

mutual
  /-- A rewrite premise's exact recursive operation stream and terminal proof
  action. No proposition, proof, or elaborated expression is serialized. -/
  structure Premise where
    terminal : PremiseTerminal
    events : Array Event := #[]
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  /-- A source-facing operation. Failed candidates are deliberately absent:
  they do not transform the expression and require no replay action. -/
  inductive Action where
    | rewrite (rule : Rule) (premises : Array Premise)
    | reduce (reduction : Reduction)
    | builtin (builtin : Builtin)
    | simproc (declarations : Array String)
    /-- Reuse of an exact result from Lean's simp cache. The nested operations
    are the source-facing operations that originally produced the cache entry,
    with positions relative to the cached expression. -/
    | cacheReuse (events : Array Event)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  /--
  One operation committed by the simplifier, expressed without an elaborated
  term or proof payload. `position` is the raw `Expr` child path at which the
  operation ran. A missing position is an explicit unsupported boundary; a
  consumer must not search for a matching redex.
  -/
  structure Event where
    position : Option (Array Nat)
    phase : Phase
    action : Action
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson
end

/-- Term-free action needed after the expression operations.  `trueIntro`
corresponds to the ordinary goal-level step used when simp changes a target to
`True`; no proof expression is serialized. -/
inductive Terminal where
  | open
  | trueIntro
  /-- A simplified local hypothesis is `False`, so it closes the main goal. -/
  | falseElim
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

/-- The committed operations in execution order. -/
structure Trace where
  events : Array Event := #[]
  terminal : Terminal := .open
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

instance : Inhabited Trace := ⟨{}⟩

/-- The exact proof-state subject simplified by one operational trace. -/
inductive Subject where
  | target
  /-- Exact parser spelling of an explicitly named `at h` subject. -/
  | namedLocal (source : String)
  | local (contextIndex : Nat)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

/-- One subject of a location-aware `simp at ...` invocation. -/
structure SubjectTrace where
  subject : Subject
  trace : Trace
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

/-- Ordered subject traces for one source `simp` invocation. -/
structure TacticTrace where
  subjects : Array SubjectTrace := #[]
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

end Lean.Meta.Simp.Operations
