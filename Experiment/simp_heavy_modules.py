#!/usr/bin/env python3
"""Generate recording or rewritten copies of selected simp-heavy Mathlib modules."""

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
OUTPUT = ROOT / ".lake" / "simp-explicit-probe"


# Each source fragment is a complete, standalone tactic line. Multiline simp
# calls and calls shared by several goals are intentionally outside the first
# target-only experiment.
CASES: dict[str, list[tuple[str, str | None]]] = {
    "Mathlib/Data/List/DropRight.lean": [
        (
            "  simp [rdrop_eq_reverse_drop_reverse]",
            """  simp_explicit [
    List.rdrop_eq_reverse_drop_reverse,
    List.reverse_append,
    List.reverse_cons,
    List.reverse_nil,
    List.nil_append,
    List.cons_append,
    List.nil_append,
    List.drop_succ_cons,
    List.rdrop_eq_reverse_drop_reverse
  ]""",
        ),
        (
            "  simp [rtake_eq_reverse_take_reverse]",
            """  simp_explicit [
    List.rtake_eq_reverse_take_reverse,
    List.reverse_append,
    List.reverse_cons,
    List.reverse_nil,
    List.nil_append,
    List.cons_append,
    List.nil_append,
    List.take_succ_cons,
    List.reverse_cons,
    List.rtake_eq_reverse_take_reverse
  ]""",
        ),
        (
            "  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]",
            None,
        ),
        (
            "  simp",
            """  simp_explicit [
    Bool.false_eq_true,
    not_false_eq_true
  ]""",
        ),
        (
            "  simp [rdropWhile, reverse_eq_iff, getLast_eq_getElem, Nat.pos_iff_ne_zero]",
            None,
        ),
        (
            "  simp only [dropWhile_eq_self_iff]",
            """  simp_explicit [
    List.dropWhile_eq_self_iff
  ]""",
        ),
        (
            "  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]",
            None,
        ),
        (
            "  simp [rtakeWhile, reverse_eq_iff]",
            None,
        ),
        ("  simp only [rdropWhile, rtakeWhile]", None),
    ],
    "Mathlib/Analysis/RCLike/Sqrt.lean": [
        ("  simp [sqrt, cpow_def, hz, div_eq_mul_inv]", None),
        (
            "  simp [abs_of_nonpos ha'.le, Real.sqrt_eq_zero', ha'.le]",
            None,
        ),
        ("    simp [h, im_eq_zero]", None),
        ("  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]", None),
        (
            "  simp",
            """  simp_explicit [
    RCLike.complexRingEquiv_apply,
    Complex.add_re,
    Complex.ofReal_re,
    Complex.mul_re,
    Complex.ofReal_re,
    Complex.I_re,
    MulZeroClass.mul_zero,
    Complex.ofReal_im,
    Complex.I_im,
    mul_one,
    sub_self,
    add_zero,
    RCLike.complexRingEquiv_apply,
    RCLike.ofReal_re,
    RCLike.ofReal_im,
    Complex.ofReal_zero,
    MulZeroClass.zero_mul,
    add_zero
  ]""",
        ),
        (
            "  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]",
            None,
        ),
        (
            "  simp [h, sqrt, map_mul]",
            None,
        ),
        (
            "  simp [mul_add]",
            """  simp_explicit [
    Complex.norm_I,
    Complex.I_re,
    add_zero,
    one_div,
    Real.sqrt_inv,
    Complex.ofReal_inv,
    sub_zero,
    one_div,
    Real.sqrt_inv,
    Complex.ofReal_inv,
    Real.sqrt_inv,
    Complex.ofReal_inv,
    mul_add,
    mul_one
  ]""",
        ),
        (
            "  simp [mul_sub, ← sub_eq_add_neg]",
            """  simp_explicit [
    norm_neg,
    Complex.norm_I,
    Complex.neg_re,
    Complex.I_re,
    neg_zero,
    add_zero,
    one_div,
    Real.sqrt_inv,
    Complex.ofReal_inv,
    sub_zero,
    one_div,
    Real.sqrt_inv,
    Complex.ofReal_neg,
    Complex.ofReal_inv,
    neg_mul,
    ← sub_eq_add_neg,
    Real.sqrt_inv,
    Complex.ofReal_inv,
    mul_sub,
    mul_one
  ]""",
        ),
    ],
}


def recording_tactic(source: str) -> str:
    indent, tactic = source[: len(source) - len(source.lstrip())], source.lstrip()
    assert tactic.startswith("simp")
    return f"{indent}simp_explicit?{tactic[len('simp') :]}"


def generate(mode: str) -> None:
    destination_root = OUTPUT / mode
    for relative, replacements in CASES.items():
        source_path = MATHLIB / relative
        text = source_path.read_text(encoding="utf-8")
        text = text.replace("module\n", "module\n\nimport ExplicitLean.SimpExplicit\n", 1)
        lines = text.splitlines()

        for source, certificate in replacements:
            indices = [index for index, line in enumerate(lines) if line == source]
            if len(indices) != 1:
                raise RuntimeError(
                    f"expected one line {source!r} in {relative}, found {len(indices)}"
                )
            if mode == "recording":
                replacement = recording_tactic(source)
            else:
                # An unsupported recorder case deliberately remains `simp` in
                # the rewritten copy so the module still provides a runnable
                # mixed-result experiment.
                if certificate is None:
                    replacement = source
                else:
                    indent = source[: len(source) - len(source.lstrip())]
                    replacement = (
                        f"{indent}-- Original body: {source.lstrip()}\n{certificate}"
                    )
            lines[indices[0] : indices[0] + 1] = replacement.splitlines()

        text = "\n".join(lines) + "\n"

        destination = destination_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
        if mode == "rewritten":
            rewritten = sum(certificate is not None for _, certificate in replacements)
            print(
                f"{destination.relative_to(ROOT)} "
                f"({rewritten}/{len(replacements)} selected calls rewritten)"
            )
        else:
            print(destination.relative_to(ROOT))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("recording", "rewritten"))
    args = parser.parse_args()
    generate(args.mode)


if __name__ == "__main__":
    main()
