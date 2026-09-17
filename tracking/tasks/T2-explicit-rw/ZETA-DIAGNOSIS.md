# `zeta` with `name`: bounded diagnosis

## Finding

The only committed T1 trace with a named `zeta` is
`test/SimpTrace/out/zeta_delta_at_hyp.json`. Its source fixture is:

```lean
example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by
  let g : Nat → Nat := fun s => s + 0
  have hg : P (g a) := hP _
  simp_trace only [g] at hg =>trace ".../zeta_delta_at_hyp.json"
```

The recorded location is `hg : P (g a)`, with steps:

```json
{"kind":"zeta", "pos":[1,0], "name":"g",
 "before":"g", "after":"fun s => s + 0"}
{"kind":"beta", "pos":[1],
 "before":"(fun s => s + 0) a", "after":"a + 0"}
```

This is not ordinary `letE` zeta. At `[1,0]` the current subterm is the
fvar `g`, whose local declaration has a value; T1's `zetaDelta` path unfolded
that value. The name is useful diagnostic metadata, but it is not needed to
identify the declaration: the fixed position already selects that fvar and
the elaborated local context carries its value. It is therefore redundant
metadata rather than semantic input. Merely dropping it while retaining the
step is not sufficient with today's T2 implementation.

## Minimal reproducers

Run from the T2 worktree (all commands use `/dev/stdin`, so no fixture is
modified).

1. Plain `zeta` fails on the named-zeta shape because T2 only accepts a `letE`:

```sh
printf '%s\n' \
  'import ExplicitLean.ExplicitRw' \
  'example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by' \
  '  let g : Nat → Nat := fun s => s + 0' \
  '  have hg : P (g a) := hP _' \
  '  explicit_rw [zeta at [1, 0]] at hg' \
  | lake env lean /dev/stdin
```

Observed: `explicit_rw: step 1: \`zeta\` at this position: the subterm is
not a \`let\`.`

2. Rendering the name as `unfold g` is not a solution: `g` is a local let,
not a global constant.

```sh
printf '%s\n' \
  'import ExplicitLean.ExplicitRw' \
  'example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by' \
  '  let g : Nat → Nat := fun s => s + 0' \
  '  have hg : P (g a) := hP _' \
  '  explicit_rw [unfold g at [1, 0]] at hg' \
  | lake env lean /dev/stdin
```

Observed: `Unknown constant \`g\``.

3. A `change` to the recorded value is accepted and preserves the intended
kernel-checked definitional transformation:

```sh
printf '%s\n' \
  'import ExplicitLean.ExplicitRw' \
  'example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by' \
  '  let g : Nat → Nat := fun s => s + 0' \
  '  have hg : P (g a) := hP _' \
  '  explicit_rw [change (fun s => s + 0) at [1, 0]] at hg' \
  '  guard_hyp hg :ₛ P ((fun s => s + 0) a)' \
  '  exact True.intro' \
  | lake env lean /dev/stdin
```

Observed: exit 0. The T4 renderer independently rejects the current JSON
rather than silently dropping the field:

```sh
PYTHONPATH=/Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline/Experiment/pipeline \
  python3 -c 'import render; print(render.render_step({"kind":"zeta","pos":[1,0],"name":"g"}))'
```

Observed: `RenderError: reduction_has_name`; T4's case is intentionally
classified as a T1/spec mismatch.

## Options

### 1. Recommended: classify local-let zeta-delta as `change`

T1 should emit `{"kind":"change", "pos": ..., "to": ...}` for a fvar
whose local declaration is unfolded, using the value rendered in the required
`pp.all` form. T2 already checks `change` by defeq, and T4 already renders it;
the emitted source is ordinary `change`, with no new tactic or simp machinery.

* Soundness: strongest existing contract. The `to` term is checked at the
  selected subterm's type and by defeq; no name lookup or search is involved.
* Compatibility: plain `letE` zeta remains unchanged. Existing named-zeta
  JSON needs regeneration or an explicitly versioned migration; the old
  record must not be silently relabelled without producing its `to` field.
* Cost: T1 classification and its fixture/expected output change; no T2
  syntax or spec kind is added. Large `pp.all` values can still hit the known
  T4 dialect refusal, which is an honest render failure rather than unsound
  replay.

### 2. Drop `name` and extend `zeta` to fvar values

Keep the JSON kind as `zeta`, omit `name`, and define T2 `zeta` to accept either
`letE` or an fvar whose local declaration has `value?`, reducing the latter.
The spec would need to document both cases; T4 would render the existing short
`zeta at [...]` form.

* Soundness: sound if the fvar branch requires a value and checks the result is
  defeq to the original; a non-let fvar must fail. The fixed position makes a
  separate textual name unnecessary.
* Compatibility: concise output and no value payload, but it changes T2's
  semantics and requires T4 to accept old named-zeta records or T1 to
  regenerate them. It also broadens a spec kind that currently means only
  `let x := v; b`.
* Cost: a T2 implementation/test change plus a spec amendment, with care around
  implementation-detail locals and local declarations lacking `value?`.

### 3. Add a distinct `zeta_delta <name>` step form

Amend the schema and add syntax/renderer support that explicitly names the
local let being unfolded, separately from ordinary `zeta` on a `letE`.

* Soundness: the replayer can verify that the selected subterm is the named
  fvar and then unfold only its local value, making intent explicit.
* Compatibility: preserves the current trace's meaning and distinguishes the
  two reductions, but requires a schema/spec amendment and coordinated T1/T2/T4
  changes. Inaccessible or hygienic local names require the existing `rename_i`
  machinery, making this more fragile for generated source.
* Cost: highest surface and migration cost for information the position and
  local context already provide.

## Recommendation

Choose option 1. The event is a definitional replacement whose portable source
operation is `change`, not `zeta` or global `unfold`; reclassifying it uses the
existing kernel-checked contract and avoids making a redundant local name part
of the generated proof. Do not simply drop `name` and leave `zeta` unchanged:
the first reproducer proves that would turn this real T1 event into a replay
failure.
