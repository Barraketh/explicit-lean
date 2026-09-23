# T79 term-free simp operations and `explicit_rw_v2`

Implemented a separate operational recorder and replay syntax without changing
the legacy `explicit_rw` format.  The recorder emits committed operations in
execution order with their exact current-expression child path, rule identity,
direction, phase, variant, extra-argument count, premise terminal summaries,
and terminal goal action.  The source-facing JSON contains no expressions,
proof terms, or fingerprints.

`explicit_rw_v2` replays the closed readable operations directly.  It supports
global, equation-indexed, and local-context rules; forward and reverse
rewrites; exact positions; explicit premise closures; beta/iota/projection/zeta
and named unfolding; hypothesis locations; and term-free terminal closure.
It does not call or import `Lean.Meta.Simp`, discover a rule, or search another
position.  Simprocs are parsed only to produce an explicit residual failure.

The Python renderer converts operation JSON to `explicit_rw_v2` source and
fails closed on unsupported operations.  Current explicit residuals are
simprocs, builtins, source-syntax/opaque rules, traversal without a principled
raw position, nested premise simplification, and the remaining uncommon
definitional operations.

Independent focused review found and the implementation fixed two major
issues before integration: legacy local-rule/local-definition fingerprints
were leaking into the new IR, and metadata child paths were one level too
shallow.  The operational IR now has narrow identity-only origin/reduction
types, and metadata traversal records child `0` exactly.

Verified checks:

- `lake build ExplicitLean:shared`
- `lake env lean test/SimpTrace/T79OperationalReplay.lean`
- `lake env lean test/ExplicitRw/Definitional.lean`
- `python3 -B Experiment/check_render_simp_operations.py` (6 tests)
- `python3 -B Experiment/check_simp_operations.py`
- `python3 -B Experiment/check_no_simp_family.py`
- `git diff --check`

The recorder regression covers declaration, contextual-local, beta, nested
application, and metadata paths.  The replay regression covers rule kinds,
all phase spellings, reverse direction, extra arguments, premises, reductions,
goal/hypothesis locations, proposition rules, exact-path refusal, and simproc
refusal.  This is not a whole-tree or simp-disabled certification claim.
