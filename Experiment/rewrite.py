#!/usr/bin/env python3
"""Create body-rewritten copies of the representative Mathlib modules."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
EXPORTS = ROOT / ".lake" / "proof-term-probe"
OUTPUT = EXPORTS / "rewritten"
PLACEHOLDER = re.compile(r"(?<![\w])_(?![\w])")


CASES = {
    "Mathlib/SetTheory/Cardinal/NatCount.lean": [
        (
            "Nat_count_le_setENCard",
            """theorem count_le_setENCard : count p n ≤ Set.encard { k | p k } := by
  simp only [Set.encard, ENat.card, Set.coe_setOf, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n""",
            """theorem count_le_setENCard {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ) :
    count p n ≤ Set.encard { k | p k } :=
{body}""",
        ),
    ],
    "Mathlib/Algebra/DualNumber.lean": [
        (
            "DualNumber_commute_eps_left",
            """theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp""",
            """theorem commute_eps_left {R : Type*} [semiringR : Semiring R] (x : DualNumber R) :
    Commute ε x :=
{body}""",
        ),
        (
            "DualNumber_range_lift",
            """theorem range_lift
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]""",
            """theorem range_lift {R : Type*} {B : Type*} {A : Type*}
    [commSemiringR : CommSemiring R] [semiringA : Semiring A] [semiringB : Semiring B]
    [algebraRA : Algebra R A] [algebraRB : Algebra R B]
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] :=
{body}""",
        ),
    ],
    "Mathlib/Algebra/ContinuedFractions/Translations.lean": [
        (
            "GenContFract_first_num_eq",
            """theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_cont_eq zeroth_s_eq]""",
            """theorem first_num_eq {K : Type*} {g : GenContFract K}
    [divisionRingK : DivisionRing K] {gp : Pair K}
    (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a :=
{body}""",
        ),
    ],
}


def main() -> None:
    for relative_path, replacements in CASES.items():
        source = MATHLIB / relative_path
        text = source.read_text(encoding="utf-8")
        for stem, original, replacement in replacements:
            occurrences = text.count(original)
            if occurrences != 1:
                raise RuntimeError(
                    f"expected one declaration block for {stem}, found {occurrences}"
                )
            body = (EXPORTS / f"{stem}.named-body.lean").read_text(
                encoding="utf-8"
            ).rstrip("\n")
            if PLACEHOLDER.search(body):
                raise RuntimeError(f"generated body for {stem} contains an _ placeholder")
            if "✝" in body:
                raise RuntimeError(f"generated body for {stem} contains an inaccessible name")
            text = text.replace(original, replacement.replace("{body}", body), 1)

        destination = OUTPUT / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
        print(destination.relative_to(ROOT))


if __name__ == "__main__":
    main()
