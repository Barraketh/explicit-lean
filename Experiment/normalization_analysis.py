#!/usr/bin/env python3
"""Measure how much of Mathlib's rewrite traffic belongs to fixed normal forms.

Lean's rewrite trace is used only as an observation mechanism.  A rewrite is
counted as normalization when its theorem and direction occur in one of the
fixed catalogs below.  The catalogs mirror the experimental normalizers in
`ExplicitLean.Normalize` or established algorithmic normalizers such as
`ring_nf`; they never inspect the module's ambient simp set.
"""

from __future__ import annotations

import re
import subprocess
import time
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"

MODULES = (
    "Mathlib/CategoryTheory/Localization/SmallHom.lean",
    "Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean",
    "Mathlib/LinearAlgebra/Vandermonde.lean",
    "Mathlib/AlgebraicGeometry/Normalization.lean",
    "Mathlib/NumberTheory/ModularForms/Derivative.lean",
)


NORMALIZERS: dict[str, tuple[str, ...]] = {
    "category": (
        "assoc",
        "Category.assoc",
        "id_comp",
        "Category.id_comp",
        "comp_id",
        "Category.comp_id",
    ),
    "functor": (
        "Functor.map_id",
        "Functor.map_comp",
        "Functor.comp_obj",
        "Functor.comp_map",
        "NatTrans.comp_app",
        "NatTrans.id_app",
    ),
    "iso": (
        "Iso.trans_hom",
        "Iso.trans_inv",
        "Iso.symm_hom",
        "Iso.symm_inv",
        "Iso.refl_hom",
        "Iso.refl_inv",
        "Iso.hom_inv_id",
        "Iso.inv_hom_id",
        "Iso.hom_inv_id_assoc",
        "Iso.inv_hom_id_assoc",
        "Iso.hom_inv_id_app",
        "Iso.inv_hom_id_app",
        "Iso.hom_inv_id_app_assoc",
        "Iso.inv_hom_id_app_assoc",
    ),
    "equiv": (
        "Equiv.trans_apply",
        "Equiv.symm_trans_apply",
        "Equiv.symm_symm",
        "Equiv.refl_apply",
        "Equiv.apply_symm_apply",
        "Equiv.symm_apply_apply",
    ),
    "algebra": (
        "add_zero",
        "AddZeroClass.add_zero",
        "zero_add",
        "AddZeroClass.zero_add",
        "mul_one",
        "MulOneClass.mul_one",
        "one_mul",
        "MulOneClass.one_mul",
        "mul_zero",
        "MulZeroClass.mul_zero",
        "zero_mul",
        "MulZeroClass.zero_mul",
        "sub_zero",
        "sub_self",
        "neg_zero",
        "zero_smul",
        "one_smul",
    ),
    "projections": (
        "Function.comp_apply",
        "Pi.zero_apply",
        "Pi.one_apply",
        "Pi.add_apply",
        "Pi.sub_apply",
        "Pi.mul_apply",
        "Pi.neg_apply",
        "Pi.pow_apply",
        "Pi.smul_apply",
    ),
    "matrix": (
        "Matrix.of_apply",
        "of_apply",
        "Matrix.transpose_apply",
        "transpose_apply",
        "Matrix.mul_apply",
        "mul_apply",
        "Matrix.submatrix_apply",
        "submatrix_apply",
    ),
    "powers": (
        "pow_zero",
        "pow_one",
        "mul_pow",
        "pow_add",
    ),
    "list": (
        "List.nil_append",
        "List.append_nil",
        "List.cons_append",
        "List.append_assoc",
        "List.reverse_nil",
        "List.reverse_cons",
        "List.reverse_append",
        "List.reverse_reverse",
        "List.drop_zero",
        "List.drop_nil",
        "List.drop_succ_cons",
        "List.take_zero",
        "List.take_nil",
        "List.take_succ_cons",
    ),
    "complex": (
        "Complex.add_re",
        "Complex.add_im",
        "Complex.sub_re",
        "Complex.sub_im",
        "Complex.mul_re",
        "Complex.mul_im",
        "Complex.neg_re",
        "Complex.neg_im",
        "Complex.ofReal_re",
        "Complex.ofReal_im",
        "Complex.ofReal_zero",
        "Complex.ofReal_one",
        "Complex.ofReal_neg",
        "Complex.ofReal_inv",
        "Complex.I_re",
        "Complex.I_im",
        "Complex.norm_I",
    ),
    "inverses": (
        "one_div",
        "inv_inv",
        "inv_one",
        "Real.sqrt_inv",
        "Complex.ofReal_inv",
    ),
}

PREFIX_NORMALIZERS = {
    "Mathlib.Tactic.RingNF.": "ring_nf",
}

REFLEXIVE = {"eq_self", "iff_self"}
TRACE_RULE = re.compile(r"^\[Meta\.Tactic\.simp\.rewrite\] (.*):\d+:$", re.MULTILINE)
SIMP_TOKEN = re.compile(r"\b(?:simp|simpa|simp_rw)\b")


def rule_matches(origin: str, rule: str) -> bool:
    return origin == rule or origin.startswith(rule + " ")


def classify(origin: str) -> str | None:
    if origin.startswith("← "):
        return None
    if origin.startswith("↓ "):
        origin = origin[2:]
    for prefix, family in PREFIX_NORMALIZERS.items():
        if origin.startswith(prefix):
            return family
    for family, rules in NORMALIZERS.items():
        if any(rule_matches(origin, rule) for rule in rules):
            return family
    return None


def trace_module(relative: str) -> tuple[list[str], float]:
    started = time.monotonic()
    result = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "-Dtrace.Meta.Tactic.simp.rewrite=true",
            str(MATHLIB / relative),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    elapsed = time.monotonic() - started
    if result.returncode != 0:
        raise RuntimeError(f"Lean failed for {relative}:\n{result.stdout[-4000:]}")
    return TRACE_RULE.findall(result.stdout), elapsed


def main() -> None:
    print(
        "| Module | LOC | simp-family tokens | Rewrite events | Covered by fixed NFs | "
        "Distinct residual rules | Seconds |"
    )
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
    residual_by_module: dict[str, Counter[str]] = {}
    family_total: Counter[str] = Counter()
    event_total = 0
    covered_total = 0

    for relative in MODULES:
        source = (MATHLIB / relative).read_text(encoding="utf-8")
        origins, elapsed = trace_module(relative)
        origins = [origin for origin in origins if origin not in REFLEXIVE]
        families = [classify(origin) for origin in origins]
        family_counts = Counter(family for family in families if family is not None)
        residual = Counter(
            origin for origin, family in zip(origins, families, strict=True) if family is None
        )
        covered = sum(family_counts.values())
        event_total += len(origins)
        covered_total += covered
        family_total.update(family_counts)
        residual_by_module[relative] = residual
        percent = 100 * covered / len(origins) if origins else 0
        print(
            f"| `{relative.removesuffix('.lean')}` | {len(source.splitlines()):,} | "
            f"{len(SIMP_TOKEN.findall(source)):,} | {len(origins):,} | "
            f"{covered:,} ({percent:.1f}%) | {len(residual):,} | {elapsed:.1f} |"
        )

    percent = 100 * covered_total / event_total if event_total else 0
    print(
        f"| **Total** | | | **{event_total:,}** | **{covered_total:,} ({percent:.1f}%)** | | |"
    )
    print("\nCovered events by normal form:")
    for family, count in family_total.most_common():
        print(f"  {family:12s} {count:5d}")
    print("\nMost frequent residual rules by module:")
    for relative, residual in residual_by_module.items():
        print(f"  {relative}")
        for origin, count in residual.most_common(12):
            print(f"    {count:4d}  {origin}")


if __name__ == "__main__":
    main()
