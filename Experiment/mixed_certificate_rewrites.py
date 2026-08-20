#!/usr/bin/env python3
"""Generate complete Mathlib copies containing materialized mixed certificates."""

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
OUTPUT = ROOT / ".lake" / "mixed-certificate-rewritten"

REWRITES: dict[str, tuple[str, str]] = {
    "Mathlib/CategoryTheory/PathCategory/Basic.lean": (
        "      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]",
        """      normalize_category
      simp_explicit [
        CategoryTheory.eqToHom_trans_assoc,
        CategoryTheory.eqToHom_refl
      ]
      normalize_category""",
    ),
    "Mathlib/CategoryTheory/Yoneda.lean": (
        "  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]",
        """  simp_explicit [
    ← CategoryTheory.Category.assoc,
    hg
  ]
  normalize_category""",
    ),
    "Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean": (
        "  simp only [assoc, inv_hom, comp_id, id_comp]",
        """  simp_explicit [
    CategoryTheory.Category.assoc,
    inv_hom
  ]
  normalize_category""",
    ),
    "Mathlib/CategoryTheory/Triangulated/Subcategory.lean": (
        "    simp only [Functor.map_inv, assoc, IsIso.inv_hom_id, comp_id, id_comp]",
        """    simp_explicit [
      CategoryTheory.Functor.map_inv,
      CategoryTheory.Category.assoc,
      CategoryTheory.IsIso.inv_hom_id
    ]
    normalize_category""",
    ),
    "Mathlib/CategoryTheory/EqToHom.lean": (
        "  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]",
        """  simp_explicit [
    CategoryTheory.eqToHom_refl,
    CategoryTheory.eqToHom_refl
  ]
  normalize_category""",
    ),
}


def main() -> None:
    original_bytes = 0
    mixed_bytes = 0
    for relative, (original, replacement) in REWRITES.items():
        text = (MATHLIB / relative).read_text(encoding="utf-8")
        text = text.replace("module\n", "module\n\nimport ExplicitLean.SimpExplicit\n", 1)
        count = text.count(original)
        if count != 1:
            raise RuntimeError(f"expected one target in {relative}, found {count}")
        indent = original[: len(original) - len(original.lstrip())]
        annotated = (
            f"{indent}/- Original mixed-certificate fragment:\n"
            f"{original}\n"
            f"{indent}-/\n"
            f"{replacement}"
        )
        text = text.replace(original, annotated, 1)
        destination = OUTPUT / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
        original_bytes += len(original.encode("utf-8"))
        mixed_bytes += len(replacement.encode("utf-8"))
        print(destination.relative_to(ROOT))
    print(
        f"materialized mixed fragments: {original_bytes} original bytes, "
        f"{mixed_bytes} mixed-certificate bytes"
    )


if __name__ == "__main__":
    main()
