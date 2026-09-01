#!/usr/bin/env python3
"""Exercise the declaration/environment oracle on bounded source pairs.

Each pair uses the same module identity and filename, so private names are
stable while the stock and applied sources live in separate temporary roots.
The accepted cases document the semantic equivalences the oracle permits; the
rejected cases make sure a changed observable declaration or environment is
fail-closed.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as boundary_source
import simp_engine_inventory as inventory
from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
MARKER = "SIMP_ENGINE_DECLARATION_ORACLE "
KIND = "simp_engine_declaration_oracle"
SCHEMA = 1
TIMEOUT = 600
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "


@dataclass(frozen=True)
class Case:
    name: str
    stock: str
    applied: str
    accepted: bool
    category: str | None = None
    private_proof_counts: tuple[int, int, int] | None = None
    detail_contains: str | None = None


def source(body: str, *, mathlib: bool = False) -> str:
    dependency = "Mathlib" if mathlib else "Lean"
    return f"module\n\nimport {dependency}\n\npublic section\n\n" + body + "\n"


EARLY_IMPORT_SOURCE = (
    "import Lean.Elab.Command\n"
    "run_cmd do\n"
    "  if (← Lean.getOptionDecls).contains `linter.style.header then\n"
    "    throwError \"oracle preloaded an unrelated Mathlib option registry\"\n"
    "theorem oracleSample : True := True.intro\n"
)


def matcher_order_source(entries: str) -> str:
    return source(
        "def match_a : Nat := 0\n"
        "def match_b : Nat := 0\n"
        "def match_c : Nat := 0\n"
        "run_cmd do\n"
        "  let info1 : Lean.Meta.MatcherInfo := {\n"
        "    numParams := 1, numDiscrs := 1, altInfos := #[],\n"
        "    uElimPos? := none, discrInfos := #[], overlaps := {} }\n"
        "  let info2 : Lean.Meta.MatcherInfo := { info1 with numParams := 2 }\n"
        f"  for (name, info) in #[{entries}] do\n"
        "    Lean.Meta.Match.addMatcherInfo name info"
    )


def async_matcher_source() -> str:
    return source(
        "open Lean Meta Elab Tactic\n"
        "@[expose] def oracleChoice (n : Nat) : Nat :=\n"
        "  match n with | 0 => 7 | n + 1 => n\n"
        "theorem oracleSample : True := by\n"
        "  run_tac do\n"
        "    let eqns ← Match.getEquationsFor `oracleChoice.match_1\n"
        "    unless isPrivateName eqns.splitterName do\n"
        "      throwError \"fixture expected a private splitter\"\n"
        "  trivial\n"
        "run_cmd do\n"
        "  let env ← getEnv\n"
        "  let name := mkPrivateName env `oracleChoice.match_1 ++ `splitter\n"
        "  unless env.constants.contains name && !env.containsOnBranch name do\n"
        "    throwError \"fixture did not reach checked-only async declaration\""
    )


def async_private_body_source(value: int, inline: str = "inline") -> str:
    return source(
        "open Lean Meta Elab Tactic\n"
        "def oracleAnchor : Nat := 0\n"
        "theorem oracleSample : True := by\n"
        "  run_tac do\n"
        "    let name := mkPrivateName (← getEnv) `oracleAnchor ++ `computation\n"
        "    realizeConst `oracleAnchor name do\n"
        "      let decl := Declaration.defnDecl {\n"
        "        name, levelParams := [], type := mkConst ``Nat,\n"
        f"        value := mkNatLit {value}, hints := .abbrev, safety := .safe }}\n"
        "      addDecl decl\n"
        "      compileDecl decl\n"
        "      let env ← Lean.ofExcept <| Lean.Compiler.setInlineAttribute "
        f"(← Lean.getEnv) name .{inline}\n"
        "      Lean.setEnv env\n"
        "  trivial\n"
        "run_cmd do\n"
        "  let env ← getEnv\n"
        "  let name := mkPrivateName env `oracleAnchor ++ `computation\n"
        "  unless env.constants.contains name && !env.containsOnBranch name do\n"
        "    throwError \"fixture did not reach checked-only async declaration\""
    )


def private_to_additive_proof_source(stem: str) -> str:
    return source(
        f"@[to_additive add{stem}ProofHelper]\n"
        f"private theorem mul{stem}ProofHelper : True := True.intro\n"
        "theorem oracleSample : True := True.intro",
        mathlib=True,
    )


def public_translation_source(target: str) -> str:
    return source(
        "theorem oracleSource : True := True.intro\n"
        "theorem oracleTargetA : True := True.intro\n"
        "theorem oracleTargetB : True := True.intro\n"
        f"insert_to_additive_translation oracleSource {target}",
        mathlib=True,
    )


def duplicate_public_translation_source(first: str, second: str) -> str:
    return source(
        "theorem oracleSource : True := True.intro\n"
        "theorem oracleTargetA : True := True.intro\n"
        "theorem oracleTargetB : True := True.intro\n"
        f"insert_to_additive_translation oracleSource {first}\n"
        "run_cmd do\n"
        "  Lean.modifyEnv (Mathlib.Tactic.ToAdditive.translations.addEntry · "
        f"(`oracleSource, {{ translation := `{second} }}))",
        mathlib=True,
    )


def generated_proof_numbering_source(first_as_term: bool) -> str:
    first = "True.intro" if first_as_term else "by exact True.intro"
    return source(
        "structure OracleProofBox where\n"
        "  first : True\n"
        "  second : (1 : Nat) = 1\n"
        "def oracleSample : OracleProofBox where\n"
        f"  first := {first}\n"
        "  second := by rfl"
    )


def generated_congruence_source(include_helper: bool, *, direct_range: bool = False) -> str:
    range_entry = (
        "  Lean.addDeclarationRanges `oracleOwner.congr_simp "
        "{ range := default, selectionRange := default }\n"
        if direct_range
        else ""
    )
    helper = (
        "run_cmd do\n"
        "  let theoremValue : TheoremVal := {\n"
        "    name := `oracleOwner.congr_simp\n"
        "    levelParams := []\n"
        "    type := mkConst ``True\n"
        "    value := mkConst ``True.intro\n"
        "  }\n"
        "  liftCoreM <| addDecl (.thmDecl theoremValue)\n"
        + range_entry
        if include_helper else ""
    )
    return source(
        "open Lean Elab Command\n"
        "def oracleOwner : Nat := 0\n"
        "namespace oracleOwner\nend oracleOwner\n"
        + helper
        + "theorem oracleSample : True := True.intro"
    )


CASES = (
    Case("async-matcher-checked-declarations", async_matcher_source(), async_matcher_source(), True),
    Case("async-private-computational-equivalence", async_private_body_source(1),
         async_private_body_source(1), True),
    Case("async-private-computational-inline-mismatch", async_private_body_source(1),
         async_private_body_source(1, "noinline"), False, "environment_delta_mismatch",
         detail_contains="observable inline attributes differ"),
    Case("async-private-computational-value-mismatch", async_private_body_source(1),
         async_private_body_source(2), False, "declaration_value_mismatch"),
    Case("early-import-option-registry", EARLY_IMPORT_SOURCE, EARLY_IMPORT_SOURCE, True),
    Case(
        "proof-body-difference",
        source("theorem oracleSample : True := by trivial"),
        source("theorem oracleSample : True := by exact True.intro"),
        True,
    ),
    Case(
        "generated-public-proof-renumbering",
        generated_proof_numbering_source(False),
        generated_proof_numbering_source(True),
        True,
    ),
    Case(
        "authored-public-proof-lookalike-renamed",
        source("namespace oracleOwner\ntheorem _proof_1 : True := True.intro\nend oracleOwner"),
        source("namespace oracleOwner\ntheorem _proof_2 : True := True.intro\nend oracleOwner"),
        False,
        "declaration_set_mismatch",
    ),
    Case(
        "generated-public-congruence-omission",
        generated_congruence_source(True),
        generated_congruence_source(False),
        True,
    ),
    Case(
        "authored-public-congruence-lookalike-omission",
        generated_congruence_source(True, direct_range=True),
        generated_congruence_source(False),
        False,
        "declaration_set_mismatch",
    ),
    Case(
        "private-to-additive-proof-translation-renamed",
        private_to_additive_proof_source("Stock"),
        private_to_additive_proof_source("Applied"),
        True,
        private_proof_counts=(2, 2, 1),
    ),
    Case(
        "public-to-additive-translation-mismatch",
        public_translation_source("oracleTargetA"),
        public_translation_source("oracleTargetB"),
        False,
        "environment_delta_mismatch",
        detail_contains="observable translations differ",
    ),
    Case(
        "duplicate-to-additive-translation-order-mismatch",
        duplicate_public_translation_source("oracleTargetA", "oracleTargetB"),
        duplicate_public_translation_source("oracleTargetB", "oracleTargetA"),
        False,
        "environment_delta_mismatch",
        detail_contains="observable translations differ",
    ),
    Case(
        "to-additive-translation-missing-endpoints",
        source(
            "insert_to_additive_translation oracleMissingSource oracleMissingTarget",
            mathlib=True,
        ),
        source(
            "insert_to_additive_translation oracleMissingSource oracleMissingTarget",
            mathlib=True,
        ),
        False,
        "environment_delta_mismatch",
        detail_contains="to_additive translation has no source declaration",
    ),
    Case(
        "module-doc-range-shift",
        source("/-! Oracle module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        "module\n\nimport Lean\n"
        "import ExplicitLean.SimpEngine.Boundary.Tactic\n\n"
        "public section\n\n/-! Oracle module documentation. -/\n\n"
        "theorem oracleSample : True := True.intro\n",
        True,
    ),
    Case(
        "module-doc-text-mismatch",
        source("/-! Stock module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        source("/-! Applied module documentation. -/\n\ntheorem oracleSample : True := True.intro"),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "derived-module-use-subset",
        source(
            "run_cmd Lean.recordExtraModUse `Mathlib.Data.Int.Cast.Basic false\n"
            "theorem oracleSample : True := True.intro", mathlib=True
        ),
        source("theorem oracleSample : True := True.intro", mathlib=True),
        True,
    ),
    Case(
        "added-module-use",
        source("theorem oracleSample : True := True.intro", mathlib=True),
        source(
            "run_cmd Lean.recordExtraModUse `Mathlib.Data.Int.Cast.Basic false\n"
            "theorem oracleSample : True := True.intro", mathlib=True
        ),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "axiom-subset-mismatch",
        source("theorem oracleSample : True := True.intro"),
        source("theorem oracleSample : True := Classical.choice ⟨True.intro⟩"),
        False,
        "axiom_subset_mismatch",
    ),
    Case(
        "defeq-computational-difference",
        source("def oracleSample : Nat := Nat.succ 0"),
        source("def oracleSample : Nat := 1"),
        True,
    ),
    Case(
        "non-defeq-data",
        source("def oracleSample : Nat := 1"),
        source("def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "type-mismatch",
        source("def oracleSample : Nat := 1"),
        source("def oracleSample : Int := 1"),
        False,
        "declaration_type_mismatch",
    ),
    Case(
        "opaque-non-proof-mismatch",
        source("opaque oracleSample : Nat := 1"),
        source("opaque oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "irreducible-non-proof-mismatch",
        source("@[irreducible] def oracleSample : Nat := 1"),
        source("@[irreducible] def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "unsafe-runtime-mismatch",
        source("unsafe def oracleSample : Nat := 1"),
        source("unsafe def oracleSample : Nat := 2"),
        False,
        "declaration_value_mismatch",
    ),
    Case(
        "public-attribute-mismatch",
        source("theorem oracleSample : (1 : Nat) = 1 := rfl"),
        source(
            "theorem oracleSample : (1 : Nat) = 1 := rfl\n"
            "attribute [simp] oracleSample"
        ),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "public-internal-looking-name-type-mismatch",
        source("theorem oracleWarmup : True ∧ True := ⟨True.intro, True.intro⟩\n"
               "theorem proof_1 : True := True.intro"),
        source("theorem oracleWarmup : True ∧ True := ⟨True.intro, True.intro⟩\n"
               "theorem proof_1 : True ∧ True := ⟨True.intro, True.intro⟩"),
        False,
        "declaration_type_mismatch",
    ),
    Case(
        "public-internal-looking-name-omission",
        source("theorem proof_1 : True := True.intro"),
        source(""),
        False,
        "declaration_set_mismatch",
    ),
    Case(
        "public-internal-looking-name-axiom-mismatch",
        source("theorem proof_1 : True := True.intro"),
        source("theorem proof_1 : True := Classical.choice ⟨True.intro⟩"),
        False,
        "axiom_subset_mismatch",
    ),
    Case(
        "public-matcher-duplicate-entry-order",
        matcher_order_source("(`match_c, info1), (`match_a, info2), (`match_b, info1), (`match_a, info1)"),
        matcher_order_source("(`match_c, info1), (`match_b, info1), (`match_a, info1), (`match_a, info2)"),
        False,
        "environment_delta_mismatch",
        detail_contains="Lean.Meta.Match.Extension.extension",
    ),
    Case(
        "private-proof-helper-omission",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source("theorem oracleSample : True := True.intro"),
        True,
    ),
    Case(
        "private-proof-helper-metadata-difference",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private opaque oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        True,
        private_proof_counts=(0, 0, 2),
    ),
    Case(
        "private-proof-inline-helper-renamed",
        source(
            "@[inline] private def stockProofHelper : True := True.intro\n"
            "theorem oracleSample : True := stockProofHelper"
        ),
        source(
            "@[inline] private def appliedProofHelper : True := True.intro\n"
            "theorem oracleSample : True := appliedProofHelper"
        ),
        True,
    ),
    Case(
        "private-proof-inline-helper-omitted",
        source(
            "@[inline] private def stockProofHelper : True := True.intro\n"
            "theorem oracleSample : True := stockProofHelper"
        ),
        source("theorem oracleSample : True := True.intro"),
        True,
    ),
    Case(
        "public-inline-attribute-mismatch",
        source("def oracleSample (n : Nat) : Nat := n\n"
               "run_cmd do\n"
               "  let env ← Lean.ofExcept <| Lean.Compiler.setInlineAttribute (← Lean.getEnv) ``oracleSample .inline\n"
               "  Lean.setEnv env"),
        source("def oracleSample (n : Nat) : Nat := n\n"
               "run_cmd do\n"
               "  let env ← Lean.ofExcept <| Lean.Compiler.setInlineAttribute (← Lean.getEnv) ``oracleSample .noinline\n"
               "  Lean.setEnv env"),
        False,
        "environment_delta_mismatch",
        detail_contains="observable inline attributes differ",
    ),
    Case(
        "private-computational-inline-attribute-mismatch",
        source(
            "@[inline] private def oraclePrivateHelper (n : Nat) : Nat := n\n"
            "def oracleSample (n : Nat) : Nat := oraclePrivateHelper n"
        ),
        source(
            "@[noinline] private def oraclePrivateHelper (n : Nat) : Nat := n\n"
            "def oracleSample (n : Nat) : Nat := oraclePrivateHelper n"
        ),
        False,
        "environment_delta_mismatch",
    ),
    Case(
        "public-matcher-metadata-mismatch",
        source("def oracleSample (n : Nat) : Nat := n"),
        source(
            "def oracleSample (n : Nat) : Nat := n\n"
            "run_cmd Lean.Meta.Match.addMatcherInfo ``oracleSample {\n"
            "  numParams := 0, numDiscrs := 1, altInfos := #[],\n"
            "  uElimPos? := none, discrInfos := #[], overlaps := {} }"
        ),
        False,
        "environment_delta_mismatch",
        detail_contains="Lean.Meta.Match.Extension.extension",
    ),
    Case(
        "private-proof-helper-type-difference",
        source(
            "private theorem oracleWarmup : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private theorem oracleWarmup : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "private theorem oraclePrivateHelper : True ∧ True := "
            "⟨True.intro, True.intro⟩\n"
            "theorem oracleSample : True := True.intro"
        ),
        True,
        private_proof_counts=(0, 0, 3),
    ),
    Case(
        "private-proof-classification-mismatch",
        source(
            "private theorem oraclePrivateHelper : True := True.intro\n"
            "theorem oracleSample : True := True.intro"
        ),
        source(
            "private def oraclePrivateHelper : Nat := 1\n"
            "theorem oracleSample : True := True.intro"
        ),
        False,
        "declaration_set_mismatch",
        detail_contains="private-proof classification differs",
    ),
    Case(
        "private-computational-omission",
        source(
            "private def oraclePrivateHelper : Nat := 1\n"
            "theorem oracleSample : True := True.intro"
        ),
        source("theorem oracleSample : True := True.intro"),
        False,
        "declaration_set_mismatch",
    ),
    Case(
        "added-axiom",
        source("theorem oracleSample : True := True.intro"),
        source(
            "axiom oracleAddedAxiom : False\n"
            "theorem oracleSample : True := oracleAddedAxiom.elim"
        ),
        False,
        "declaration_set_mismatch",
    ),
)


def parse_report(output: str) -> dict[str, object]:
    reports = [
        json.loads(line.split(MARKER, 1)[1].strip())
        for line in output.splitlines()
        if line.startswith(MARKER)
    ]
    if len(reports) != 1 or not isinstance(reports[0], dict):
        raise RuntimeError(f"oracle emitted {len(reports)} canonical markers:\n{output}")
    report = reports[0]
    if report.get("kind") != KIND or report.get("schema") != SCHEMA:
        raise RuntimeError(f"oracle marker identity mismatch: {report}")
    return report


def check_selector_options_round_trip(root: Path) -> None:
    """A recorder artifact must replay under the oracle's compiler options.

    This is intentionally an end-to-end source pair: the expected selector
    options come from a fresh command-line recording, then the generated
    selector is elaborated by the declaration oracle.  It catches accidental
    drift in the oracle frontend options while preserving the selector's
    strict equality check.
    """
    stock_root = root / "selector-options-stock"
    applied_root = root / "selector-options-applied"
    stock_path = stock_root / "Mathlib" / "SelectorOptions.lean"
    applied_path = applied_root / "Mathlib" / "SelectorOptions.lean"
    stock_path.parent.mkdir(parents=True)
    applied_path.parent.mkdir(parents=True)
    call = 'simp_engine_boundary_record_applied "selector-options-regression" only'
    stock = (
        "module\n\n"
        "public import Mathlib.Logic.Basic\n"
        "import ExplicitLean.SimpEngine.Boundary\n\n"
        "public theorem selectorOptionsSample : True := by\n"
        f"  {call}\n"
    )
    stock_path.write_text(stock, encoding="utf-8")
    dylib = ROOT / ".lake" / "build" / "lib" / "libexplicitLean_ExplicitLean.dylib"
    command = inventory.lean_command(stock_path)
    command.insert(3, f"--load-dynlib={dylib.resolve()}")
    environment, nonce = protocol.recording_subprocess_environment()
    recorded = run_process(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=TIMEOUT, check=False, env=environment,
    )
    if recorded.returncode != 0:
        raise RuntimeError(f"selector-options recording failed:\n{recorded.stdout}")
    reports = protocol.parse_framed_json_lines(
        recorded.stdout, marker=ARTIFACT_MARKER, expected_nonce=nonce,
        label="selector-options recording",
    )
    if len(reports) != 1 or not isinstance(reports[0], dict):
        raise RuntimeError(f"selector-options recording emitted {len(reports)} artifacts")
    report = reports[0]
    replacement = boundary_source.format_report_variants([report])
    applied_path.write_text(stock.replace(call, replacement), encoding="utf-8")
    module = "Mathlib.SelectorOptions"
    command = [
        sys.executable, str(ROOT / "Experiment" / "lean_toolchain_cache.py"),
        "oracle", module, str(stock_path), str(applied_path),
    ]
    checked = run_process(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=TIMEOUT, check=False,
    )
    oracle = parse_report(checked.stdout)
    if checked.returncode != 0 or oracle.get("status") != "success":
        raise RuntimeError(
            "selector-options oracle rejected a freshly recorded selector:\n"
            f"{checked.stdout}"
        )


def check_case(case: Case, root: Path, ordinal: int) -> None:
    stock_dir = root / f"{ordinal:02d}-stock"
    applied_dir = root / f"{ordinal:02d}-applied"
    stock_dir.mkdir()
    applied_dir.mkdir()
    stock_path = stock_dir / "Fixture.lean"
    applied_path = applied_dir / "Fixture.lean"
    stock_path.write_text(case.stock, encoding="utf-8")
    applied_path.write_text(case.applied, encoding="utf-8")
    module = "Experiment.SimpEngine.DeclarationOracleFixture"
    command = [
        sys.executable,
        str(ROOT / "Experiment/lean_toolchain_cache.py"),
        "oracle",
        module,
        str(stock_path),
        str(applied_path),
    ]
    completed = run_process(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=TIMEOUT,
        check=False,
    )
    report = parse_report(completed.stdout)
    accepted = report.get("status") == "success" and completed.returncode == 0
    if accepted != case.accepted:
        raise RuntimeError(
            f"{case.name}: expected accepted={case.accepted}, got {report};\n"
            f"{completed.stdout}"
        )
    if case.category is not None and report.get("failureCategory") != case.category:
        raise RuntimeError(
            f"{case.name}: expected category {case.category!r}, got {report};\n"
            f"{completed.stdout}"
        )
    detail = report.get("failureDetail")
    if case.category is not None and (not isinstance(detail, str) or not detail):
        raise RuntimeError(
            f"{case.name}: expected a failure detail, got {report};\n{completed.stdout}"
        )
    if case.private_proof_counts is not None:
        actual_counts = (
            report.get("stockOnlyPrivateProofCount"),
            report.get("appliedOnlyPrivateProofCount"),
            report.get("checkedDeclarationCount"),
        )
        if actual_counts != case.private_proof_counts:
            raise RuntimeError(
                f"{case.name}: expected private-proof/accounted counts "
                f"{case.private_proof_counts}, got {actual_counts};\n{completed.stdout}"
            )
    if case.detail_contains is not None and (
        not isinstance(detail, str) or case.detail_contains not in detail
    ):
        raise RuntimeError(
            f"{case.name}: expected detail containing {case.detail_contains!r}, "
            f"got {detail!r};\n{completed.stdout}"
        )


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="declaration-oracle-", dir=ROOT / ".lake") as raw:
        root = Path(raw)
        check_selector_options_round_trip(root)
        for ordinal, case in enumerate(CASES):
            check_case(case, root, ordinal)
    print(
        "declaration oracle: "
        f"{sum(case.accepted for case in CASES)} accepted-equivalence and "
        f"{sum(not case.accepted for case in CASES)} fail-closed cases passed"
    )


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.SubprocessError) as error:
        print(f"declaration oracle checker failed: {error}", file=sys.stderr)
        raise SystemExit(1)
