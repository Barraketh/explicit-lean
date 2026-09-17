# T3-compliance -- adversarial review round 3

Fresh reviewer; RESULT.md was not trusted. Every claim re-run independently,
including a corpus sweep written from scratch rather than the bundled test.
Merge-base used: `6eaed5035d8b3caf682d4f3a7db7aee38f72fdb6`.

## Verdict

**NO DEFECTS.**

All three round-2 defects are genuinely fixed. The round-2 rewrite replaced the
backward character scan with structural delimiter matching, and that change
holds up under attack: I found **no false negative in any compilable Lean** and
**no false positive** anywhere, including an independent 8264-file sweep whose
attribute oracle I wrote myself. RESULT.md is accurate, including its one
substantive Lean claim, which I re-derived by compiling the counterfactual.

## Round 2 defects: all three confirmed fixed

- **Defect 1 fixed (8 `@[...]` spellings).** All seven listed lines plus the
  U+2190 arrow reproducer are now clean (`0 simp-family finding(s)`, rc=0).
- **Defect 2 fixed (3 `attribute` command spellings).** `local attribute`,
  `scoped attribute`, `scoped[Pointwise] attribute`, `open Foo in attribute`
  are all clean. The command-position guard is intact: `exact foo attribute
  [simp]` is still flagged at line 1, column 22.
- **Defect 3 fixed (untested).** 46 tests (round 2: 38). The spellings are
  really pinned: `grep -cE` over `check_simp_family_lint.py` gives `local
  attribute` 2, `scoped attribute` 1, `scoped[` 3, `in attribute` 4, `grind` 2,
  `aesop` 2, `deprecated` 1, `to_dual` 1 -- all were 0 in round 2.

## Attacks that found nothing (evidence)

1. **Unbalanced delimiters in strings and comments (task 2's main attack).**
   `-- [`, `/- ] -/`, `"["`, `"@["`, `-- @[`, `/- @[simp] -/` each placed before
   a real `by simp`: **all six still flagged**. Masking runs before the matcher,
   so a delimiter inside a comment or string cannot unbalance the scan. Valid
   escaped-quote strings (`"escaped \" quote"`), trailing escaped backslashes,
   raw strings, `s!"..."`, char literals `'a'`, identifier primes `h'`, and
   nested `/- /- -/ -/` all leave following code scanned.
2. **Bracketed non-attribute contexts.** Constructed 12, all correctly flagged:
   `all_goals [simp]`, `first | simp | rfl`, `conv in [simp] => rfl`,
   `omega [simp]`, `rw [h] <;> simp`, `exact foo [simp]`, `apply f (by simp)`,
   `refine ⟨by simp, ?_⟩`, `def l : List Tac := [simp]`, `have := by simp`,
   `induction ... | zero => simp`. A `[...]` only shields when opened by `@` or
   the `attribute` keyword in command position, so tactic-list brackets do not.
3. **`@[simp]` + a real tactic on one line: the tactic is flagged, not the
   attribute.** Exactly one finding each, at the tactic's column:
   `@[simp] theorem foo : p := by simp` -> col 31;
   `@[simp, norm_cast] ... := by norm_num` -> col 42;
   `@[to_additive (attr := simp)] ... := by dsimp` -> col 53;
   `attribute [simp] foo` + a later `by simp` line -> line 2, col 21.
4. **Command prefixes from the brief.** Clean, as they must be: `attribute
   [simp] foo in`, `set_option ... in @[simp]` (same line and split),
   `#guard_msgs in @[simp]`, `section`-scoped `attribute [local simp]`,
   `attribute [scoped simp]`, `open Classical in`, `variable {x} in`,
   `private`/`protected attribute [simp]`, and attribute groups split across
   lines with `--` and `/- -/` comments inside the group.
5. **The `in` command-position heuristic does not shield real code.** The
   shield requires the literal keyword `attribute` immediately before `[`. The
   only inputs I could shield -- `conv in attribute [simp] => rfl`,
   `exact (foo in attribute [simp])`, `for x in attribute [simp] do` -- are
   **Lean parse errors** (`lake env lean`: "unexpected token 'attribute';
   expected term", "unexpected token 'in'"), so they cannot occur in compilable
   code. `grep -rnE '\bin\b[^-]*\battribute *\[' Mathlib` over the pinned
   corpus: **0 lines**. Not a defect. Bare `conv in x => simp`, `for x in l do
   simp`, `open Foo in` + `by simp`, `set_option ... in` + `by simp` all flag.
6. **Unterminated constructs go clean, but are parse errors.** `def s :=
   "unterminated`, `/- unterminated`, `@[simp` + newline, `attribute [simp` +
   newline swallow a following `by simp`. Each is rejected by Lean itself
   ("unterminated string literal"; "unexpected token 'theorem'; expected ']'"),
   so no compilable file reaches this path. Reported as behaviour, not a defect.
7. **Nesting depth.** `_MAX_BRACKET_DEPTH = 16`: an attribute argument nested
   20 groups deep is flagged. Depth 3 (the documented corpus maximum) is clean.
   Unreachable in real Lean; reported as behaviour, not a defect.
8. **`syntax`/`macro`/`elab "simp"` declarations are clean** -- the token sits
   inside a string literal, which the masker blanks. `initialize
   registerTraceClass `simp` **is flagged** (backtick name, not a string). Only
   3 pinned files declare such syntax and generated regions never contain them,
   so neither behaviour affects the deliverable. Reported as the brief asked.
9. **Identifier adjacency.** `simp'`, `simp.foo`, `simple`, `Nat.simp_foo`,
   `Simp.Config.default`, `@[simps]` clean; consistent with rounds 1-2.
10. **Loader rejection, 12 fresh temp DBs built from the real JSON.** All
    violations rejected, including the brief's `conv`-hidden case: `conv =>\n
    dsimp only [f]`, `conv_lhs => dsimp`, `dsimp only [f]`, `exact h <;> dsimp
    only [f]`, `exact h\n norm_cast` -- these five are caught **only** by the
    new lint, not by the pre-existing `BANNED_SEARCH_PATTERN`. Plus `push_cast`,
    `norm_num`, `simpa`, `field_simp`, `<;> simp_all`. A clean replacement still
    loads. The lint alone treats a retained `-- Original simp:` comment as clean;
    that entry is rejected by the older `replacement == source` guard instead.

## Independent corpus sweep (my own oracle, not the bundled test)

I re-implemented the attribute oracle from scratch -- backward delimiter scan
over masked text, checking for `@` or a trailing `attribute` keyword -- and ran
it over every pinned file. It agrees with RESULT.md exactly:

```
files=8264 total_findings=124182 elapsed=332.3s
ATTRIBUTE-DERIVED FINDINGS (should be 0): 0
```

This reproduces RESULT.md's "0 of 124,182" figure independently, so the claim
is not a tautology of the implementation under test.

## Checks run

| Check | Result |
| --- | --- |
| `check_simp_family_lint.py` (fast) | PASS, 46 tests, 0.04 s |
| `check_simp_family_lint.py --sweep` | PASS, 46 tests, **329.5 s**, 55 MB RSS |
| `check_manual_overlay.py` | PASS, 6 tests, 0 s |
| `check_simp_manual_overrides.py` | PASS, rc=0, 496 s, "passed" |
| `check_campaign_supervisor_v10.py` | PASS, rc=0, 1 s |
| `check_campaign_worker.py` | PASS, rc=0, 1 s |
| `check_simp_manual_composition.py` | FAIL, rc=1, 266 s -- pre-existing |
| `lake env lean` x4 `test/Compliance/*.lean` | PASS, rc=0, **0 bytes** output, 5.5-7.5 s, RSS 0.81-0.87 GB |
| `splice.py` regen + `git status` | byte-identical, worktree clean |
| Lint over 21 shipped replacements | 21 entries, **0** findings, 0 `erw` |
| Loader rejection, 12 temp DBs | all violations rejected, clean one loads |
| Independent 8264-file sweep | 124182 findings, **0** attribute-derived |

The dependent set was rediscovered independently with `grep -rln -E
"simp_manual_overrides|manual_overlay|simp_family_lint" Experiment/check_*.py`
and matches round 2's six. `check_simp_manual_overrides.py` is the one that
exercises `load_database` against the shipped JSON and re-elaborates the patched
modules, so the wiring is confirmed end to end on the real database.

**Pre-existing failure re-confirmed a third time, independently.** I ran
`check_simp_manual_composition.py` in the **untouched main checkout**
(`/Users/ptsier/projects/explicit-lean`, HEAD `6febc7d`, containing none of
T3's changes): rc=1, "manual simp composition failed: generated renderer
continuation indentation leaves no line budget" -- identical to the worktree.
Not a T3 defect.

## Scope

`git diff --name-only <merge-base>` lists **12** paths, all task-owned. The JSON
diff is exactly the two `replacement` strings -- `source`, byte ranges, ids and
digests untouched. `simp_manual_overrides.py` is **+9 lines**, purely the
`import` and the `assert_clean` call. `Experiment/manual_overlay.py` is
**unmodified**. Both control files hash to exactly the `moduleSourceSha256`
recorded in the JSON (`35c8da59...`, `05c54873...`), and `diff control
replacement` differs only in the tactic block (Unitization 268, EpiMono 243).
No `sorry`, `admit`, `axiom` or `erw` anywhere in `test/Compliance/`.

## RESULT.md honesty

**60 lines exactly (at the cap). Accurate; no overstatement found.**

- The sweep line ("0 of 124,182 findings are attribute-derived, over all 8264
  pinned files") reproduces exactly under my independent oracle.
- The round-2 narrowing is honestly recorded: RESULT.md explicitly flags its own
  round-1 sweep line as "**too broad**" and names the 18 cases round 2 found.
  Self-correction rather than quiet revision.
- The `--sweep` runtime is stated as 304 s; I measured **329.5 s**. Machine
  variance on the same order, not a misstatement.
- The Lean claim "a one-step `rw [map_zero, zero_add]` fails (`zero_add` also
  fires on the RHS)" is **true**: I built that exact variant and compiled it --
  `error: unsolved goals`. The shipped three-tactic form compiles clean.
- The known-limitation paragraph correctly scopes the composition failure as
  pre-existing and names the owning function.
