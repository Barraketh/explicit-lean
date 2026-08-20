#!/usr/bin/env python3
"""Generate Mathlib copies whose proofs use named normalization phases."""

from pathlib import Path

from simp_heavy_modules import CASES as EXACT_REPLAY_CASES


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
OUTPUT = ROOT / ".lake" / "normalization-probe" / "rewritten"

EARLIER_MODULES = {
    "Mathlib/Data/List/DropRight.lean",
    "Mathlib/Analysis/RCLike/Sqrt.lean",
}


REPLACEMENTS: dict[str, list[tuple[str, str]]] = {
    "Mathlib/Data/List/DropRight.lean": [
        (
            "  simp [rdrop_eq_reverse_drop_reverse]",
            "  normalize_list using [List.rdrop_eq_reverse_drop_reverse]",
        ),
        (
            "  simp [rtake_eq_reverse_take_reverse]",
            "  normalize_list using [List.rtake_eq_reverse_take_reverse]",
        ),
    ],
    "Mathlib/Analysis/RCLike/Sqrt.lean": [
        (
            "  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, "
            "Complex.sqrt_of_nonneg (by simpa)]\n  simp",
            "  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, "
            "Complex.sqrt_of_nonneg (by simpa)]\n"
            "  normalize_rclike\n  normalize_complex\n  normalize_algebra",
        ),
        (
            "  simp [mul_add]",
            "  normalize_complex\n  normalize_algebra\n  normalize_inverses\n  ring_nf",
        ),
        (
            "  simp [mul_sub, ← sub_eq_add_neg]",
            "  normalize_complex\n  normalize_algebra\n  normalize_inverses\n  ring_nf",
        ),
    ],
    "Mathlib/CategoryTheory/Localization/SmallHom.lean": [
        (
            "  simp only [equiv_comp, assoc]",
            "  simp only [equiv_comp]\n  normalize_category",
        ),
    ],
    "Mathlib/LinearAlgebra/Vandermonde.lean": [
        (
            "  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]",
            "  normalize_matrix\n  simp only [vandermonde_apply]\n  normalize_powers",
        ),
        (
            "  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]",
            "  normalize_matrix\n  simp only [vandermonde_apply]\n  normalize_powers",
        ),
    ],
    "Mathlib/AlgebraicGeometry/Normalization.lean": [
        (
            "    simp only [← Iso.inv_comp_eq, Category.assoc]",
            "    normalize_category using [← Iso.inv_comp_eq]",
        ),
        (
            "  simp only [app_eq_appLE, Category.assoc, map_appLE, appLE_map]",
            "  normalize_category using [app_eq_appLE, map_appLE, appLE_map]",
        ),
    ],
    "Mathlib/NumberTheory/ModularForms/Derivative.lean": [
        (
            "  simp only [normalizedDerivOfComplex, Pi.add_apply]",
            "  normalize_projections using [normalizedDerivOfComplex]",
        ),
        (
            "  simp only [normalizedDerivOfComplex, Pi.sub_apply]",
            "  normalize_projections using [normalizedDerivOfComplex]",
        ),
        (
            "  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]",
            "  normalize_projections using [normalizedDerivOfComplex, smul_eq_mul]",
        ),
        (
            "  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]",
            "  normalize_projections using [normalizedDerivOfComplex]",
        ),
        (
            "  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]",
            "  normalize_projections using [normalizedDerivOfComplex]",
        ),
    ],
}


def main() -> None:
    original_bytes = 0
    replacement_bytes = 0
    module_bytes: dict[str, tuple[int, int]] = {}
    for relative, replacements in REPLACEMENTS.items():
        source = (MATHLIB / relative).read_text(encoding="utf-8")
        source = source.replace("module\n", "module\n\nimport ExplicitLean.Normalize\n", 1)
        for original, replacement in replacements:
            count = source.count(original)
            if count != 1:
                raise RuntimeError(
                    f"expected one occurrence of {original!r} in {relative}, found {count}"
                )
            indent = original.splitlines()[0][
                : len(original.splitlines()[0]) - len(original.splitlines()[0].lstrip())
            ]
            source = source.replace(
                original,
                f"{indent}/- Original normalization fragment:\n{original}\n{indent}-/\n{replacement}",
                1,
            )
            original_bytes += len(original.encode("utf-8"))
            replacement_bytes += len(replacement.encode("utf-8"))
        module_bytes[relative] = (
            sum(len(original.encode("utf-8")) for original, _ in replacements),
            sum(len(replacement.encode("utf-8")) for _, replacement in replacements),
        )
        destination = OUTPUT / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(source, encoding="utf-8")
        print(f"{destination.relative_to(ROOT)} ({len(replacements)} replacements)")
    print(
        f"normalization fragments: {original_bytes} original bytes, "
        f"{replacement_bytes} replacement bytes"
    )

    harder_original = sum(
        original for module, (original, _) in module_bytes.items() if module not in EARLIER_MODULES
    )
    harder_replacement = sum(
        replacement
        for module, (_, replacement) in module_bytes.items()
        if module not in EARLIER_MODULES
    )

    earlier_sources = {
        "Mathlib/Data/List/DropRight.lean": {
            "  simp [rdrop_eq_reverse_drop_reverse]",
            "  simp [rtake_eq_reverse_take_reverse]",
        },
        "Mathlib/Analysis/RCLike/Sqrt.lean": {
            "  simp",
            "  simp [mul_add]",
            "  simp [mul_sub, ← sub_eq_add_neg]",
        },
    }
    exact_bytes = 0
    for module, cases in EXACT_REPLAY_CASES.items():
        for source, certificate in cases:
            if source in earlier_sources.get(module, set()):
                if certificate is None:
                    raise RuntimeError(f"missing exact certificate for {module}: {source}")
                exact_bytes += len(certificate.encode("utf-8"))
    earlier_original = sum(
        len(source.encode("utf-8")) for sources in earlier_sources.values() for source in sources
    )
    earlier_normalized = sum(
        len(fragment.encode("utf-8"))
        for fragment in (
            "  normalize_list using [List.rdrop_eq_reverse_drop_reverse]",
            "  normalize_list using [List.rtake_eq_reverse_take_reverse]",
            "  normalize_rclike\n  normalize_complex\n  normalize_algebra",
            "  normalize_complex\n  normalize_algebra\n  normalize_inverses\n  ring_nf",
            "  normalize_complex\n  normalize_algebra\n  normalize_inverses\n  ring_nf",
        )
    )
    print(
        f"five earlier long calls: {earlier_original} ambient-simp bytes, "
        f"{exact_bytes} exact-replay bytes, {earlier_normalized} normalization bytes"
    )
    print(
        f"ten harder fragments: {harder_original} original bytes, "
        f"{harder_replacement} normalization bytes"
    )


if __name__ == "__main__":
    main()
