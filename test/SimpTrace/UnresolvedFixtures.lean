/-
`simp_trace` fixtures whose calls are **classified unresolved**.

These are goals stock `simp` proves and `simp_trace` traces, but for which some
part of the trace cannot be expressed in `simp-trace-v1`.  The tactic leaves
stock simp's goal state and reports one `simp_trace unresolved: <reason>` line,
so *this file is expected to exit 1* — that is the behaviour under test.

They live apart from `Fixtures.lean` so that file stays a clean green gate
(REVIEW-4 defect 4): `Experiment/check_simp_trace.py` fails on a nonzero exit of
any positive fixture, and would trip on these.

Compile with `lake env lean test/SimpTrace/UnresolvedFixtures.lean` from the
repository root.  The checker compares the traces these still write, exactly as
for a positive fixture; what it does not require is a zero exit.
-/
import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic

namespace ExplicitLean.SimpTrace.UnresolvedFixtures

/-- `zeta := false` on a `let` whose body is simplified.  `letToHave` converts
the `let` to a `have` (recorded as a `change`), and `simpHaveTelescope` then
simplifies the whole telescope through the generic `MonadSimp SimpM` instance,
which dispatches to *stock* `simp`.  Those inner rewrites carry no position in
the fork's convention, so the telescope rewrite is recorded as one `change` and
the call is classified unresolved.  The goal state still matches stock. -/
example (f : Nat → Nat) (a : Nat) :
    (let x := a; f (x + 0)) = (let x := a; f x) := by
  simp_trace (config := { zeta := false })
    =>trace "test/SimpTrace/out/let_body_zeta_off.json"

/-- Negative control for REVIEW-5 2: an `Iff`-returning simproc whose `propext`
argument is **not** a single lemma application — here `Iff.intro` of two
hand-built implications, the shape Mathlib's `existsAndEq` produces. Unwrapping
`propext` must not hand back a lemma name; the firing stays an `eq` step, and
since no ordinary tactic proves the equation the call is the classified
`unresolved:simproc:<name>` the spec defines. The goal state is stock simp's. -/
def UnresTag (n : Nat) : Prop := n = n

open Lean Meta Simp in
simproc_decl unresTagProc (UnresTag _) := fun e => do
  let_expr UnresTag n := e | return .continue
  let lhs := mkApp (mkConst ``UnresTag) n
  let fwd := .lam `h lhs (mkConst ``True.intro) .default
  -- `UnresTag n` unfolds to `n = n`, so `rfl` inhabits it.
  let bwd := .lam `h (mkConst ``True)
    (mkApp2 (mkConst ``rfl [1]) (mkConst ``Nat) n) .default
  let inner := mkApp4 (mkConst ``Iff.intro) lhs (mkConst ``True) fwd bwd
  let pf := mkApp3 (mkConst ``propext) lhs (mkConst ``True) inner
  return .done { expr := mkConst ``True, proof? := pf }

attribute [simp] unresTagProc

example (k : Nat) : UnresTag k := by
  simp_trace =>trace "test/SimpTrace/out/propext_nonlemma.json"

end ExplicitLean.SimpTrace.UnresolvedFixtures
