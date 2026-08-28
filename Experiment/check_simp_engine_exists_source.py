#!/usr/bin/env python3
"""Authoritative source gate for ``ExistsAndEq.existsAndEq``.

The committed closure histogram identified 65 complete Mathlib modules which
contain 77 source ``simp``/``simp only`` sites reaching this semantic simproc.
This gate locks that module/site manifest directly and records every supported
simp-family occurrence in each complete source file.  It
computes complete/nondeferred occurrence statistics for every supported site,
then materializes only a complete occurrence which actually contains a
committed ExistsAndEq result.  This keeps unrelated complete ``simp`` calls
out of the targeted replay phase while retaining the full source inventory.

The semantic simproc itself is deliberately accounted for independently of
the historical source-site terminal status.  The committed report was
recorded before this semantic support was available, so its deferral reasons
select the fixture set but do not determine current replay eligibility.
Complete/nondeferred statistics and current targeted authorization are both
recorded. The gate partitions every committed result observation into either
an ``existentialEqualityElim`` candidate or an explicit unsupported result,
then partitions every candidate into authorized replay or an accepted event
inside a still-deferred source occurrence, retaining execution multiplicity.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-exists-source"

EXISTS_NAME = [["str", "ExistsAndEq"], ["str", "existsAndEq"]]
RESULT_DISPOSITIONS = {"done", "visit", "continueSome"}

# These values are locked after the first print-current audit.  The module
# tuple is (all supported source occurrences, complete/nondeferred source
# occurrences, deferred source occurrences, unsuccessful executions, targeted
# materialized occurrences, targeted replay executions, Exists committed
# observations, semantic candidates, and Exists observations in deferred source
# occurrences).
EXPECTED_TOTALS = {
    "occurrences": 1984,
    "completeOccurrences": 1306,
    "deferredOccurrences": 678,
    "unsuccessful": 0,
    "recordingExecutions": 2140,
    "targetedMaterializedOccurrences": 16,
    "targetedReplayExecutions": 17,
    "existsCommittedResults": 94,
    "existsSemanticCandidates": 90,
    "existsUnsupportedResults": 4,
    "existsAcceptedUntargeted": 73,
    "existsResultsInDeferredOccurrences": 77,
    "existsAuthorized": 17,
    "existsSourceSites": 77,
}

# Keep the locked table explicit: it makes a drift in one complete module fail
# at the module boundary rather than being hidden by aggregate totals.
EXPECTED_MODULE_TOTALS: dict[str, tuple[int, ...]] = {
    "Mathlib/Algebra/Order/Antidiag/Nat.lean": (11, 7, 4, 0, 0, 0, 1, 1, 1),
    "Mathlib/Algebra/Order/Antidiag/Pi.lean": (20, 12, 8, 0, 0, 0, 1, 1, 1),
    "Mathlib/CategoryTheory/Sites/Sieves.lean": (62, 58, 4, 0, 0, 0, 1, 1, 1),
    "Mathlib/Combinatorics/Graph/Basic.lean": (31, 21, 10, 0, 0, 0, 1, 1, 1),
    "Mathlib/Combinatorics/Graph/Maps.lean": (6, 4, 2, 0, 0, 0, 2, 2, 2),
    "Mathlib/Combinatorics/Matroid/Constructions.lean": (31, 23, 8, 0, 0, 0, 1, 1, 1),
    "Mathlib/Combinatorics/SimpleGraph/Cayley.lean": (10, 3, 7, 0, 0, 0, 3, 3, 3),
    "Mathlib/Combinatorics/SimpleGraph/Maps.lean": (29, 21, 8, 0, 0, 0, 1, 1, 1),
    "Mathlib/Computability/Language.lean": (18, 15, 3, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Fin/Tuple/Basic.lean": (102, 19, 83, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Finset/Prod.lean": (15, 5, 10, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Finset/Sym.lean": (17, 12, 5, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Finsupp/AList.lean": (10, 6, 4, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Fintype/List.lean": (6, 6, 0, 0, 1, 1, 1, 1, 0),
    "Mathlib/Data/Int/GCD.lean": (16, 7, 9, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/List/NatAntidiagonal.lean": (6, 1, 5, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/List/Permutation.lean": (65, 56, 9, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/List/ProdSigma.lean": (5, 3, 2, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Multiset/Bind.lean": (67, 50, 17, 0, 0, 0, 2, 2, 2),
    "Mathlib/Data/Multiset/Count.lean": (15, 9, 6, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Nat/Factorization/Basic.lean": (68, 28, 40, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Nat/Factorization/Root.lean": (27, 2, 25, 0, 0, 0, 2, 2, 2),
    "Mathlib/Data/Ordmap/Invariants.lean": (46, 12, 34, 0, 0, 0, 3, 3, 3),
    "Mathlib/Data/Seq/Basic.lean": (140, 110, 30, 0, 1, 2, 2, 2, 1),
    "Mathlib/Data/Set/Functor.lean": (6, 1, 5, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Set/Image.lean": (43, 28, 15, 0, 2, 2, 3, 3, 1),
    "Mathlib/Data/Set/NAry.lean": (15, 6, 9, 0, 2, 2, 2, 2, 0),
    "Mathlib/Data/Set/Prod.lean": (65, 41, 24, 0, 0, 0, 1, 1, 1),
    "Mathlib/Data/Sum/Interval.lean": (23, 5, 18, 0, 0, 0, 4, 4, 4),
    "Mathlib/Geometry/Convex/Cone/Face/Basic.lean": (15, 13, 2, 0, 0, 0, 1, 1, 1),
    "Mathlib/GroupTheory/Coset/Defs.lean": (13, 11, 2, 0, 0, 0, 2, 2, 2),
    "Mathlib/GroupTheory/Descent.lean": (2, 1, 1, 0, 1, 1, 1, 1, 0),
    "Mathlib/GroupTheory/Goursat.lean": (10, 8, 2, 0, 0, 0, 1, 1, 1),
    "Mathlib/GroupTheory/IsSubnormal.lean": (9, 8, 1, 0, 0, 0, 1, 1, 1),
    "Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Shift.lean": (26, 14, 12, 0, 1, 1, 1, 1, 0),
    "Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean": (33, 6, 27, 0, 0, 0, 1, 1, 1),
    "Mathlib/LinearAlgebra/Goursat.lean": (8, 6, 2, 0, 0, 0, 1, 1, 1),
    "Mathlib/LinearAlgebra/RootSystem/CartanMatrix.lean": (22, 16, 6, 0, 0, 0, 1, 1, 1),
    "Mathlib/Logic/Encodable/Basic.lean": (14, 10, 4, 0, 0, 0, 1, 1, 1),
    "Mathlib/MeasureTheory/Constructions/Polish/Basic.lean": (16, 13, 3, 0, 0, 0, 1, 1, 1),
    "Mathlib/MeasureTheory/Constructions/SimpleGraph.lean": (4, 4, 0, 0, 1, 1, 1, 1, 0),
    "Mathlib/MeasureTheory/Function/JacobianOneDim.lean": (37, 32, 5, 0, 0, 0, 1, 1, 1),
    "Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean": (49, 47, 2, 0, 2, 2, 3, 3, 0),
    "Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean": (18, 11, 7, 0, 1, 1, 1, 1, 0),
    "Mathlib/NumberTheory/Divisors.lean": (74, 27, 47, 0, 0, 0, 8, 8, 8),
    "Mathlib/NumberTheory/ModularForms/Cusps.lean": (32, 21, 11, 0, 0, 0, 1, 0, 1),
    "Mathlib/Order/Filter/Bases/Basic.lean": (36, 34, 2, 0, 1, 1, 1, 1, 0),
    "Mathlib/Order/Filter/Ultrafilter/Basic.lean": (4, 3, 1, 0, 0, 0, 1, 1, 1),
    "Mathlib/Order/InitialSeg.lean": (6, 3, 3, 0, 0, 0, 1, 1, 1),
    "Mathlib/Order/Partition/Basic.lean": (17, 9, 8, 0, 0, 0, 1, 1, 1),
    "Mathlib/Probability/ConditionalProbability.lean": (18, 15, 3, 0, 0, 0, 1, 1, 1),
    "Mathlib/Probability/Independence/Process/Basic.lean": (10, 7, 3, 0, 1, 1, 1, 1, 0),
    "Mathlib/Probability/Process/Stopping.lean": (122, 111, 11, 0, 1, 1, 1, 1, 0),
    "Mathlib/RingTheory/DedekindDomain/GaussLemma.lean": (7, 5, 2, 0, 1, 1, 1, 1, 0),
    "Mathlib/RingTheory/Ideal/Operations.lean": (45, 35, 10, 0, 0, 0, 2, 2, 2),
    "Mathlib/RingTheory/MvPowerSeries/Rename.lean": (41, 23, 18, 0, 0, 0, 3, 1, 3),
    "Mathlib/RingTheory/OreLocalization/Basic.lean": (18, 17, 1, 0, 0, 0, 1, 1, 1),
    "Mathlib/RingTheory/ZariskisMainTheorem.lean": (52, 38, 14, 0, 0, 0, 1, 1, 1),
    "Mathlib/SetTheory/Cardinal/Basic.lean": (25, 18, 7, 0, 0, 0, 1, 1, 1),
    "Mathlib/SetTheory/ZFC/Basic.lean": (36, 18, 18, 0, 0, 0, 1, 1, 1),
    "Mathlib/Tactic/ComputeAsymptotics/Multiseries/Corecursion.lean": (68, 53, 15, 0, 0, 0, 2, 2, 2),
    "Mathlib/Tactic/ComputeAsymptotics/Multiseries/Defs.lean": (41, 34, 7, 0, 0, 0, 2, 1, 2),
    "Mathlib/Tactic/NormNum/Irrational.lean": (26, 21, 5, 0, 0, 0, 1, 1, 1),
    "Mathlib/Topology/Algebra/GroupWithZero.lean": (6, 5, 1, 0, 0, 0, 1, 1, 1),
    "Mathlib/Topology/MetricSpace/CoveringNumbers.lean": (49, 38, 11, 0, 0, 0, 1, 1, 1),
}

# Minimal frozen evidence extracted from the full committed histogram. Keeping
# the source-site IDs, multiplicities, and phases here makes this gate runnable
# from a clean checkout without retaining the large ignored shard directory.
EXPECTED_SOURCE_SITES: dict[
    str, dict[str, tuple[int, tuple[tuple[str, int], ...]]]
] = {
    "Mathlib/Algebra/Order/Antidiag/Nat.lean": {"12a5e9537fec54b8": (1, (("pre", 1),))},
    "Mathlib/Algebra/Order/Antidiag/Pi.lean": {"beeba6671aaee4f0": (1, (("pre", 1),))},
    "Mathlib/CategoryTheory/Sites/Sieves.lean": {"ae4883d8e1bbb99a": (1, (("pre", 1),))},
    "Mathlib/Combinatorics/Graph/Basic.lean": {"f0e2b107ab44c0a5": (1, (("pre", 1),))},
    "Mathlib/Combinatorics/Graph/Maps.lean": {"41a1d52561519b68": (2, (("pre", 2),))},
    "Mathlib/Combinatorics/Matroid/Constructions.lean": {"88aeea2a7c46a8e6": (1, (("pre", 1),))},
    "Mathlib/Combinatorics/SimpleGraph/Cayley.lean": {
        "96771aa94e5d0e32": (1, (("pre", 1),)),
        "d38aa1a62e4efb4b": (2, (("pre", 2),)),
    },
    "Mathlib/Combinatorics/SimpleGraph/Maps.lean": {"c03a90017bceca4d": (1, (("pre", 1),))},
    "Mathlib/Computability/Language.lean": {"ebf581486cca859d": (1, (("pre", 1),))},
    "Mathlib/Data/Fin/Tuple/Basic.lean": {"fd8c011efcf233e2": (1, (("pre", 1),))},
    "Mathlib/Data/Finset/Prod.lean": {"cb225bce35d9faf6": (1, (("pre", 1),))},
    "Mathlib/Data/Finset/Sym.lean": {"cb39dacfcfdc262f": (1, (("pre", 1),))},
    "Mathlib/Data/Finsupp/AList.lean": {"d7066d64d3d7dbf8": (1, (("pre", 1),))},
    "Mathlib/Data/Fintype/List.lean": {"8aa6ff1f762b53e1": (1, (("pre", 1),))},
    "Mathlib/Data/Int/GCD.lean": {"479b67fe090b18a6": (1, (("pre", 1),))},
    "Mathlib/Data/List/NatAntidiagonal.lean": {"88074418ed2ba9f3": (1, (("pre", 1),))},
    "Mathlib/Data/List/Permutation.lean": {"1d82e3375864d4d6": (1, (("pre", 1),))},
    "Mathlib/Data/List/ProdSigma.lean": {"282c9b2f90d4c358": (1, (("pre", 1),))},
    "Mathlib/Data/Multiset/Bind.lean": {
        "3695d7ae5d6c6ce4": (1, (("pre", 1),)),
        "e7cfdf37edff2e58": (1, (("pre", 1),)),
    },
    "Mathlib/Data/Multiset/Count.lean": {"b6311a699c0dd357": (1, (("pre", 1),))},
    "Mathlib/Data/Nat/Factorization/Basic.lean": {"55aaf5f8ca48e199": (1, (("pre", 1),))},
    "Mathlib/Data/Nat/Factorization/Root.lean": {
        "41d0249300a8d777": (1, (("pre", 1),)),
        "99ba4177c2596ac7": (1, (("pre", 1),)),
    },
    "Mathlib/Data/Ordmap/Invariants.lean": {"e9c92723cf9d01bd": (3, (("pre", 3),))},
    "Mathlib/Data/Seq/Basic.lean": {
        "9053d5fee6edf871": (1, (("pre", 1),)),
        "e0ed1a594894e9a3": (1, (("pre", 1),)),
    },
    "Mathlib/Data/Set/Functor.lean": {"f589f5a8d9287c9c": (1, (("pre", 1),))},
    "Mathlib/Data/Set/Image.lean": {
        "40be17a0f2b9ca7f": (1, (("pre", 1),)),
        "62ca05e2fd6f6ff3": (1, (("pre", 1),)),
        "b22a4b034f416e83": (1, (("pre", 1),)),
    },
    "Mathlib/Data/Set/NAry.lean": {
        "13d4e08c7e9ea632": (1, (("pre", 1),)),
        "cc16fe110c5a4a9d": (1, (("pre", 1),)),
    },
    "Mathlib/Data/Set/Prod.lean": {"c93b3763b6e9e164": (1, (("pre", 1),))},
    "Mathlib/Data/Sum/Interval.lean": {
        "4bf39a26bafa7356": (2, (("pre", 2),)),
        "fc2231ade4442914": (2, (("pre", 2),)),
    },
    "Mathlib/Geometry/Convex/Cone/Face/Basic.lean": {"9d7383722dd627d9": (1, (("pre", 1),))},
    "Mathlib/GroupTheory/Coset/Defs.lean": {
        "2b20c2fbe5f73d26": (1, (("pre", 1),)),
        "4273302d32e690dc": (1, (("pre", 1),)),
    },
    "Mathlib/GroupTheory/Descent.lean": {"4a8a21192d569bc6": (1, (("pre", 1),))},
    "Mathlib/GroupTheory/Goursat.lean": {"056c7f20e7d3b9e3": (1, (("pre", 1),))},
    "Mathlib/GroupTheory/IsSubnormal.lean": {"81bfe2c2b2afa1e9": (1, (("pre", 1),))},
    "Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Shift.lean": {"7bf022bea72c876e": (1, (("pre", 1),))},
    "Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean": {"d56575d97f4aa91b": (1, (("pre", 1),))},
    "Mathlib/LinearAlgebra/Goursat.lean": {"088eeba93973710e": (1, (("pre", 1),))},
    "Mathlib/LinearAlgebra/RootSystem/CartanMatrix.lean": {"81017cc1a6d047b4": (1, (("pre", 1),))},
    "Mathlib/Logic/Encodable/Basic.lean": {"3851064866f505d7": (1, (("pre", 1),))},
    "Mathlib/MeasureTheory/Constructions/Polish/Basic.lean": {"8873a10c6cc024b1": (1, (("pre", 1),))},
    "Mathlib/MeasureTheory/Constructions/SimpleGraph.lean": {"703aa52294fe7e3c": (1, (("pre", 1),))},
    "Mathlib/MeasureTheory/Function/JacobianOneDim.lean": {"fa77598f0ba8a937": (1, (("pre", 1),))},
    "Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean": {
        "57a7a1a9bce077c3": (2, (("pre", 2),)),
        "9eb5883914758ad3": (1, (("pre", 1),)),
    },
    "Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean": {"131a91c86f893378": (1, (("pre", 1),))},
    "Mathlib/NumberTheory/Divisors.lean": {
        "6d85a2e9bcacd57c": (7, (("pre", 7),)),
        "92cab15fdfe93692": (1, (("pre", 1),)),
    },
    "Mathlib/NumberTheory/ModularForms/Cusps.lean": {"34695177947b0592": (1, (("post", 1),))},
    "Mathlib/Order/Filter/Bases/Basic.lean": {"39e2fab1ab8edcc2": (1, (("pre", 1),))},
    "Mathlib/Order/Filter/Ultrafilter/Basic.lean": {"e33d7182094c2fd3": (1, (("pre", 1),))},
    "Mathlib/Order/InitialSeg.lean": {"9ee6c31279f08dca": (1, (("pre", 1),))},
    "Mathlib/Order/Partition/Basic.lean": {"75a2ebdd940ad5fd": (1, (("pre", 1),))},
    "Mathlib/Probability/ConditionalProbability.lean": {"5cf3dc413d51f5dc": (1, (("pre", 1),))},
    "Mathlib/Probability/Independence/Process/Basic.lean": {"c5cbbf1d6d15a305": (1, (("pre", 1),))},
    "Mathlib/Probability/Process/Stopping.lean": {"1f95b87563a40384": (1, (("pre", 1),))},
    "Mathlib/RingTheory/DedekindDomain/GaussLemma.lean": {"f415e0116ff7dc76": (1, (("pre", 1),))},
    "Mathlib/RingTheory/Ideal/Operations.lean": {"7c556be92841e65a": (2, (("pre", 2),))},
    "Mathlib/RingTheory/MvPowerSeries/Rename.lean": {
        "8800de8e09335986": (1, (("pre", 1),)),
        "a4dd8523996f0262": (2, (("pre", 2),)),
    },
    "Mathlib/RingTheory/OreLocalization/Basic.lean": {"37deeffabd4febbf": (1, (("pre", 1),))},
    "Mathlib/RingTheory/ZariskisMainTheorem.lean": {"0d5bf93b6c78c698": (1, (("pre", 1),))},
    "Mathlib/SetTheory/Cardinal/Basic.lean": {"699b9b272892f89b": (1, (("pre", 1),))},
    "Mathlib/SetTheory/ZFC/Basic.lean": {"2fa7bd61efab33de": (1, (("pre", 1),))},
    "Mathlib/Tactic/ComputeAsymptotics/Multiseries/Corecursion.lean": {"7100cf56e9964473": (2, (("pre", 2),))},
    "Mathlib/Tactic/ComputeAsymptotics/Multiseries/Defs.lean": {"65e6fc686ffe1c39": (2, (("pre", 2),))},
    "Mathlib/Tactic/NormNum/Irrational.lean": {"7bd21e94ed52f38c": (1, (("pre", 1),))},
    "Mathlib/Topology/Algebra/GroupWithZero.lean": {"9c1c26f56a37b4a0": (1, (("pre", 1),))},
    "Mathlib/Topology/MetricSpace/CoveringNumbers.lean": {"398af9cb1b8a921c": (1, (("pre", 1),))},
}

if EXPECTED_SOURCE_SITES.keys() != EXPECTED_MODULE_TOTALS.keys():
    raise RuntimeError("ExistsAndEq locked module/site manifests disagree")

RECORD = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORD occurrence=(\S+) certificate=(\S+) "
    r"deferredSubjects=(\d+) subjects=(\d+)"
)
REPLAY = re.compile(r"SIMP_ENGINE_SOURCE_REPLAY occurrence=(\S+)")
UNSUCCESSFUL = re.compile(r"SIMP_ENGINE_SOURCE_UNSUCCESSFUL occurrence=(\S+)")
RECORDER_FAILURE = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORDER_FAILURE occurrence=(\S+)"
)


def name_components(value: object) -> list[str]:
    """Validate a serialized Lean ``Name`` and return display components."""
    if not isinstance(value, list):
        raise ValueError(f"simproc/candidate name is not an array: {value!r}")
    result: list[str] = []
    for component in value:
        if (
            not isinstance(component, list)
            or len(component) != 2
            or component[0] not in {"str", "num"}
        ):
            raise ValueError(f"invalid name component: {component!r}")
        if component[0] == "str":
            if not isinstance(component[1], str):
                raise ValueError(f"invalid string name component: {component!r}")
            result.append(component[1])
        else:
            if (
                not isinstance(component[1], int)
                or isinstance(component[1], bool)
                or component[1] < 0
            ):
                raise ValueError(f"invalid numeric name component: {component!r}")
            result.append(f"#{component[1]}")
    return result


def is_exists(value: object) -> bool:
    return isinstance(value, list) and value == EXISTS_NAME


def decoded_simproc_observations(subject: dict[str, object]) -> list[dict[str, object]]:
    """Decode and validate one compressed schema-27 simproc trace."""
    trace = subject.get("simprocs")
    if not isinstance(trace, dict):
        raise ValueError("subject simproc trace is not an object")
    dictionary = trace.get("dictionary")
    order = trace.get("order")
    if not isinstance(dictionary, list) or not isinstance(order, list):
        raise ValueError("subject simproc dictionary/order is not an array")
    for observation in dictionary:
        if not isinstance(observation, dict):
            raise ValueError("simproc dictionary entry is not an object")
        # Validate dictionary entries not reached by order as well.  Otherwise
        # malformed compressed data could be silently hidden by a short trace.
        name_components(observation.get("name"))
    result: list[dict[str, object]] = []
    for index in order:
        if (
            not isinstance(index, int)
            or isinstance(index, bool)
            or not 0 <= index < len(dictionary)
        ):
            raise ValueError(f"invalid simproc dictionary index: {index!r}")
        result.append(dictionary[index])
    return result


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    return json.loads(query.stdout.strip())


def module_key(module: str) -> str:
    """Return a stable scratch-tree key without relying on source names."""
    return module.removeprefix("Mathlib/").removesuffix(".lean").replace(
        "/", "__"
    ).replace(".", "_")


def inventory(path: Path, module: str) -> tuple[bytes, list[dict[str, object]]]:
    source = path.read_bytes()
    entries = [
        entry
        for entry in coverage.syntax_inventory_file(path, module, 600)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if not entries:
        raise RuntimeError(f"source fixture has no supported simp calls: {module}")
    return source, entries


def inventory_all(modules: list[str]) -> dict[str, tuple[bytes, list[dict[str, object]]]]:
    """Run the syntax inventory once for all 65 complete source modules."""
    paths = [str(coverage.MATHLIB / module) for module in modules]
    command = [
        "lake",
        "env",
        "lean",
        "--run",
        "Experiment/SimpEngineInventory.lean",
        *paths,
    ]
    code, output, _duration = coverage.run(command, timeout=1800)
    if code:
        raise RuntimeError(f"batch syntax inventory failed:\n{output}")
    by_path: dict[str, list[dict[str, object]]] = defaultdict(list)
    for line in output.splitlines():
        if not line.startswith("{"):
            continue
        entry = json.loads(line)
        path = str(Path(str(entry.pop("file"))).resolve())
        by_path[path].append(entry)
    result: dict[str, tuple[bytes, list[dict[str, object]]]] = {}
    for module in modules:
        path = coverage.MATHLIB / module
        all_entries = by_path.get(str(path.resolve()), [])
        entries: list[dict[str, object]] = []
        source = path.read_bytes()
        for entry in all_entries:
            entry["module"] = module
            entry["id"] = coverage.occurrence_id(
                module, int(entry["startByte"]), int(entry["endByte"])
            )
            if entry["kind"] in coverage.SUPPORTED_KINDS:
                entries.append(entry)
        if not entries:
            raise RuntimeError(f"source fixture has no supported simp calls: {module}")
        result[module] = (source, entries)
    return result


def recording_copy(
    key: str,
    module: str,
    source: bytes,
    entries: list[dict[str, object]],
    certificate_directory: Path,
) -> Path:
    def replacement(entry: dict[str, object]) -> str:
        occurrence = str(entry["id"])
        return (
            f"simp_engine_source_recording {json.dumps(occurrence)} "
            f"{json.dumps(str(certificate_directory))}"
        )

    source = coverage.rewrite_simp_heads(source, entries, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = OUTPUT / "record" / key / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def targeted_materialized_copy(
    key: str,
    module: str,
    source: bytes,
    entries: list[dict[str, object]],
    certificates: dict[str, list[Path]],
    targeted_occurrences: set[str],
) -> Path:
    chosen = [
        entry for entry in entries if str(entry["id"]) in targeted_occurrences
    ]

    def replacement(entry: dict[str, object]) -> str:
        occurrence = str(entry["id"])
        terms = sorted(
            {path.read_text(encoding="utf-8") for path in certificates[occurrence]}
        )
        if not terms:
            raise RuntimeError(f"targeted occurrence has no certificate source: {occurrence}")
        array_source = coverage.lean_string_array_source(terms, int(entry["column"]))
        return (
            f"simp_engine_apply {json.dumps(occurrence)} "
            f"(certificates := {array_source})"
        )

    source = coverage.rewrite_simp_heads(source, chosen, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = OUTPUT / "materialized" / key / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def compile_copy(destination: Path, dynlib: str, timeout: int) -> tuple[int, str]:
    command = coverage.lean_command(destination)
    command.insert(3, f"--load-dynlib={dynlib}")
    code, output, _duration = coverage.run(command, timeout=timeout)
    destination.with_suffix(".log").write_text(output, encoding="utf-8")
    return code, output


def deferred_is_unrelated(subject: dict[str, object]) -> bool:
    """Return whether a subject's deferral is provably not ExistsAndEq."""
    reason = subject.get("deferred")
    if reason is None:
        return False
    if not isinstance(reason, dict):
        raise ValueError("subject deferred reason is not an object")
    simproc = reason.get("simproc") or reason.get("simprocAndCustomDischarger")
    if isinstance(simproc, dict):
        name = simproc.get("name")
        name_components(name)
        return not is_exists(name)
    # A custom discharger cannot be ExistsAndEq itself.
    return "customDischarger" in reason


def deferred_includes_exists(subject: dict[str, object]) -> bool:
    """Return whether the subject's deferral explicitly names ExistsAndEq."""
    reason = subject.get("deferred")
    if not isinstance(reason, dict):
        return False
    simproc = reason.get("simproc") or reason.get("simprocAndCustomDischarger")
    if not isinstance(simproc, dict):
        return False
    name = simproc.get("name")
    name_components(name)
    return is_exists(name)


def validate_derivation(semantics: dict[str, object]) -> None:
    """Validate the schema-27 existential-equality witness shape."""
    if set(semantics) != {"existentialEqualityElim"}:
        raise ValueError(f"unexpected ExistsAndEq candidate semantics: {semantics!r}")
    elim = semantics["existentialEqualityElim"]
    if not isinstance(elim, dict) or not isinstance(elim.get("derivation"), dict):
        raise ValueError("ExistsAndEq candidate lacks existential derivation")
    derivation = elim["derivation"]
    route = derivation.get("route")
    if not isinstance(route, list) or any(
        step not in {"andLeft", "andRight", "existsBody"} for step in route
    ):
        raise ValueError("invalid ExistsAndEq derivation route")
    if derivation.get("binderSide") not in {"left", "right"}:
        raise ValueError("invalid ExistsAndEq derivation binder side")
    replacement = derivation.get("replacement")
    if not isinstance(replacement, dict) or not isinstance(
        replacement.get("binderDepth"), int
    ):
        raise ValueError("invalid ExistsAndEq derivation replacement")
    reference = replacement.get("reference")
    if not isinstance(reference, dict) or not isinstance(reference.get("path"), list):
        raise ValueError("invalid ExistsAndEq derivation reference")
    if not isinstance(reference.get("fingerprint"), str):
        raise ValueError("invalid ExistsAndEq derivation reference fingerprint")


def candidate_covers_observation(
    event: dict[str, object],
    fold: dict[str, object],
    candidate: dict[str, object],
    observation: dict[str, object],
) -> bool:
    """Mirror Replay's candidate/observation coverage check for this name."""
    if event.get("path") != observation.get("path"):
        return False
    if event.get("invocationOrdinal") != observation.get("phaseInvocationOrdinal"):
        return False
    if fold.get("phase") != observation.get("phase"):
        return False
    if not observation.get("executed") or observation.get("outputSize") is None:
        return False
    fields = (
        ("procedureKind", "procedureKind"),
        ("setIndex", "setIndex"),
        ("inputFingerprint", "inputFingerprint"),
        ("outputFingerprint", "outputFingerprint"),
        ("numExtraArgs", "numExtraArgs"),
        ("disposition", "stepDisposition"),
        ("proofPresent", "proofPresent"),
        ("cache", "cache"),
    )
    if any(candidate.get(lhs) != observation.get(rhs) for lhs, rhs in fields):
        return False
    return observation.get("outputChanged") == (
        candidate.get("inputFingerprint") != candidate.get("outputFingerprint")
    )


def analyze_subject(subject: dict[str, object]) -> dict[str, object]:
    """Validate one subject and count Exists observations/candidates."""
    observations = decoded_simproc_observations(subject)
    all_exists_observations = [
        observation for observation in observations if is_exists(observation.get("name"))
    ]
    exists_observations = [
        observation
        for observation in all_exists_observations
        if observation.get("stepDisposition") in RESULT_DISPOSITIONS
    ]
    passive_exists_observations = [
        observation
        for observation in all_exists_observations
        if observation.get("stepDisposition") not in RESULT_DISPOSITIONS
    ]
    for observation in exists_observations:
        if not observation.get("executed") or not observation.get("proofPresent"):
            raise ValueError("ExistsAndEq result observation lacks execution/proof")
    for observation in passive_exists_observations:
        # ExistsAndEq is intentionally pinned as a no-result observation when
        # executed.  An unexecuted dphase observation is likewise an explicit
        # no-effect boundary.  Either may be presented with the same
        # expression many times while another candidate is being searched,
        # but neither authorizes replay itself.
        if observation.get("stepDisposition") != "continueNone":
            raise ValueError(
                "unexpected non-result ExistsAndEq disposition: "
                f"{observation.get('stepDisposition')!r}"
            )
        if (
            observation.get("outputChanged")
            or observation.get("proofPresent")
            or observation.get("cache") is not None
            or observation.get("outputSize") is not None
            or observation.get("inputFingerprint")
            != observation.get("outputFingerprint")
        ):
            raise ValueError("malformed passive ExistsAndEq observation")

    program = subject.get("program")
    if not isinstance(program, dict):
        raise ValueError("subject program is not an object")
    events = program.get("events")
    if not isinstance(events, list):
        raise ValueError("subject program events is not an array")
    candidates: list[tuple[dict[str, object], dict[str, object], dict[str, object]]] = []
    for event in events:
        if not isinstance(event, dict):
            raise ValueError("program event is not an object")
        operation = event.get("operation")
        if not isinstance(operation, dict):
            raise ValueError("program event operation is not an object")
        semantic = operation.get("semanticSimproc")
        if semantic is None:
            continue
        if not isinstance(semantic, dict):
            raise ValueError("semantic simproc operation is not an object")
        fold = semantic.get("fold")
        if not isinstance(fold, dict):
            raise ValueError("semantic simproc fold is not an object")
        fold_candidates = fold.get("candidates")
        if not isinstance(fold_candidates, list):
            raise ValueError("semantic simproc candidates is not an array")
        for candidate in fold_candidates:
            if not isinstance(candidate, dict):
                raise ValueError("semantic simproc candidate is not an object")
            if not is_exists(candidate.get("declaration")):
                continue
            semantics = candidate.get("semantics")
            if not isinstance(semantics, dict):
                raise ValueError("ExistsAndEq candidate semantics is not an object")
            validate_derivation(semantics)
            if candidate.get("procedureKind") != "simp" or candidate.get("numExtraArgs") != 0:
                raise ValueError("ExistsAndEq candidate procedure metadata changed")
            candidates.append((event, fold, candidate))

    deferred = subject.get("deferred") is not None
    if len(candidates) > len(exists_observations):
        raise ValueError("more ExistsAndEq candidates than result observations")
    cursor = 0
    for event, fold, candidate in candidates:
        found = None
        for index in range(cursor, len(exists_observations)):
            if candidate_covers_observation(
                event, fold, candidate, exists_observations[index]
            ):
                found = index
                break
        if found is None:
            raise ValueError("ExistsAndEq candidate does not cover a result observation")
        cursor = found + 1
    unsupported = len(exists_observations) - len(candidates)
    if unsupported and not deferred:
        raise ValueError(
            "unsupported ExistsAndEq result did not defer the subject"
        )
    return {
        "observations": len(exists_observations),
        "passiveObservations": len(passive_exists_observations),
        "candidates": len(candidates),
        "unsupported": unsupported,
        "deferred": deferred,
        "deferredByExists": deferred_includes_exists(subject),
        "deferredUnrelated": bool(
            exists_observations and deferred_is_unrelated(subject)
        ),
        "phases": Counter(observation.get("phase") for observation in exists_observations),
    }


def parse_recording(
    module: str,
    entries: list[dict[str, object]],
    certificate_directory: Path,
    output: str,
) -> tuple[dict[str, list[int]], dict[str, list[Path]], dict[str, list[dict[str, object]]], Counter[str]]:
    known = {str(entry["id"]) for entry in entries}
    outcomes: dict[str, list[int]] = defaultdict(list)
    certificates: dict[str, list[Path]] = defaultdict(list)
    stats: dict[str, list[dict[str, object]]] = defaultdict(list)
    recorded_paths: list[Path] = []
    for match in RECORD.finditer(output):
        occurrence, certificate, deferred, subjects = match.groups()
        if occurrence not in known:
            raise RuntimeError(f"unknown occurrence in source log for {module}: {occurrence}")
        certificate_path = Path(certificate)
        if not certificate_path.is_file():
            raise RuntimeError(f"certificate source was not written: {certificate_path}")
        try:
            payload = json.loads(certificate_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"invalid certificate source: {certificate_path}") from error
        payload_subjects = payload.get("subjects")
        if not isinstance(payload_subjects, list) or len(payload_subjects) != int(subjects):
            raise RuntimeError(
                f"source log/certificate subject mismatch for {occurrence}: "
                f"log={subjects}, certificate={len(payload_subjects) if isinstance(payload_subjects, list) else payload_subjects!r}"
            )
        actual_deferred = sum(
            1
            for subject in payload_subjects
            if isinstance(subject, dict) and subject.get("deferred") is not None
        )
        if actual_deferred != int(deferred):
            raise RuntimeError(
                f"source log/certificate deferred mismatch for {occurrence}: "
                f"log={deferred}, certificate={actual_deferred}"
            )
        certificate_engine = payload.get("engine")
        if not isinstance(certificate_engine, dict):
            raise RuntimeError(f"certificate engine is missing: {certificate_path}")
        certificate_schema = certificate_engine.get("certificateSchema")
        if (
            not isinstance(certificate_schema, int)
            or isinstance(certificate_schema, bool)
            or certificate_schema < 26
        ):
            raise RuntimeError(
                f"certificate schema is too old at {certificate_path}: "
                f"{certificate_schema!r}"
            )
        subject_stats: list[dict[str, object]] = []
        for subject in payload_subjects:
            if not isinstance(subject, dict):
                raise RuntimeError(f"certificate subject is not an object: {certificate_path}")
            try:
                subject_stats.append(analyze_subject(subject))
            except ValueError as error:
                raise RuntimeError(f"invalid ExistsAndEq certificate {certificate_path}: {error}") from error
        outcomes[occurrence].append(int(deferred))
        certificates[occurrence].append(certificate_path)
        stats[occurrence].append({
            "subjects": subject_stats,
            "observations": sum(int(s["observations"]) for s in subject_stats),
            "candidates": sum(int(s["candidates"]) for s in subject_stats),
            "unsupported": sum(int(s["unsupported"]) for s in subject_stats),
            "phases": sum((s["phases"] for s in subject_stats), Counter()),
            "deferredUnrelated": sum(
                int(s["observations"]) for s in subject_stats if s["deferredUnrelated"]
            ),
        })
        recorded_paths.append(certificate_path)

    unsuccessful = Counter(match.group(1) for match in UNSUCCESSFUL.finditer(output))
    unknown_unsuccessful = set(unsuccessful) - known
    if unknown_unsuccessful:
        raise RuntimeError(
            f"unknown unsuccessful occurrence in source log for {module}: "
            f"{unknown_unsuccessful}"
        )
    recorder_failures = set(RECORDER_FAILURE.findall(output))
    if recorder_failures:
        raise RuntimeError(f"source recorder failures for {module}: {recorder_failures}")

    emitted_files = set(certificate_directory.glob("*.json"))
    if emitted_files != set(recorded_paths):
        raise RuntimeError(
            f"certificate log/file mismatch for {module}: "
            f"logged={sorted(map(str, set(recorded_paths)))} files={sorted(map(str, emitted_files))}"
        )
    return outcomes, certificates, stats, unsuccessful


def main() -> None:
    unlocked = "--print-current" in sys.argv[1:]

    # This is a dedicated scratch root.  The broad and focused source gates
    # use different roots and are not touched here.
    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    OUTPUT.mkdir(parents=True)

    started = time.monotonic()
    dynlib = dynamic_library()
    aggregate = Counter()
    module_results: dict[str, tuple[int, ...]] = {}
    exists_source_sites: set[str] = set()
    exists_phase_counts: Counter[str] = Counter()
    exists_authorized = 0
    exists_accepted_untargeted = 0
    module_names = sorted(EXPECTED_MODULE_TOTALS)
    inventories = inventory_all(module_names)
    print(
        f"SIMP_ENGINE_EXISTS_SOURCE_INVENTORY modules={len(inventories)} "
        f"occurrences={sum(len(entries) for _source, entries in inventories.values())} "
        f"elapsed={time.monotonic()-started:.1f}s",
        flush=True,
    )

    for index, module in enumerate(module_names, 1):
        path = coverage.MATHLIB / module
        if not path.is_file():
            raise RuntimeError(f"committed ExistsAndEq module source is missing: {path}")
        source, entries = inventories[module]
        known = {str(entry["id"]) for entry in entries}
        expected_exists = EXPECTED_SOURCE_SITES[module]
        certificate_directory = OUTPUT / "certificates" / module_key(module)
        recorded = recording_copy(
            module_key(module), module, source, entries, certificate_directory
        )
        code, _output = compile_copy(recorded, dynlib, timeout=1200)
        if code:
            raise RuntimeError(
                f"source recording failed for {module}; see {recorded.with_suffix('.log')}"
            )
        recording_output = recorded.with_suffix(".log").read_text(encoding="utf-8")
        outcomes, certificates, cert_stats, unsuccessful = parse_recording(
            module, entries, certificate_directory, recording_output
        )
        complete_occurrences = {
            occurrence
            for occurrence, executions in outcomes.items()
            if executions and all(deferred == 0 for deferred in executions)
        }
        deferred_occurrences = {
            occurrence
            for occurrence, executions in outcomes.items()
            if any(subjects > 0 for subjects in executions)
        }
        not_executed = known - outcomes.keys() - unsuccessful.keys()
        if not_executed:
            raise RuntimeError(
                f"source recording was not total for {module}: {sorted(not_executed)}"
            )

        exists_results = sum(int(stats["observations"]) for values in cert_stats.values() for stats in values)
        exists_candidates = sum(int(stats["candidates"]) for values in cert_stats.values() for stats in values)
        exists_unsupported = sum(
            int(stats["unsupported"]) for values in cert_stats.values() for stats in values
        )
        if exists_candidates + exists_unsupported != exists_results:
            raise RuntimeError(
                f"ExistsAndEq certificate accounting mismatch in {module}: "
                f"observations={exists_results}, candidates={exists_candidates}, "
                f"unsupported={exists_unsupported}"
            )
        module_sites = {
            occurrence for occurrence, values in cert_stats.items()
            if any(int(stats["observations"]) > 0 for stats in values)
        }
        if module_sites != expected_exists.keys():
            raise RuntimeError(
                f"ExistsAndEq source-site accounting mismatch in {module}: "
                f"expected={sorted(expected_exists)}, got={sorted(module_sites)}"
            )
        for occurrence, expected in expected_exists.items():
            values = cert_stats[occurrence]
            actual_count = sum(int(stats["observations"]) for stats in values)
            actual_phases: Counter[str] = Counter()
            for stats in values:
                actual_phases.update(stats["phases"])
            if (actual_count, tuple(sorted(actual_phases.items()))) != expected:
                raise RuntimeError(
                    f"ExistsAndEq locked source-site evidence changed in {module}:"
                    f"{occurrence}: expected={expected}, "
                    f"got={(actual_count, tuple(sorted(actual_phases.items())))}"
                )
        targeted_occurrences = module_sites & complete_occurrences
        targeted_replay_executions = 0
        if targeted_occurrences:
            materialized = targeted_materialized_copy(
                module_key(module), module, source, entries, certificates,
                targeted_occurrences
            )
            code, materialized_output = compile_copy(materialized, dynlib, timeout=1200)
            if code:
                raise RuntimeError(
                    f"targeted materialized module failed for {module}; "
                    f"see {materialized.with_suffix('.log')}"
                )
            actual_replays = Counter(
                match.group(1) for match in REPLAY.finditer(materialized_output)
            )
            expected_replays = Counter(
                {occurrence: len(outcomes[occurrence]) for occurrence in targeted_occurrences}
            )
            if actual_replays != expected_replays:
                raise RuntimeError(
                    f"targeted materialized execution mismatch in {module}: "
                    f"expected {expected_replays}, got {actual_replays}"
                )
            targeted_replay_executions = sum(actual_replays.values())
        module_phases: Counter[str] = Counter()
        for values in cert_stats.values():
            for stats in values:
                module_phases.update(stats["phases"])
        for occurrence, values in cert_stats.items():
            if not any(int(stats["observations"]) for stats in values):
                continue
            if occurrence in targeted_occurrences:
                exists_authorized += sum(int(stats["candidates"]) for stats in values)
            else:
                # A current source occurrence outside the targeted complete
                # set must be deferred.  This is a reporting classification
                # for the containing tactic, not candidate credit; require
                # that the current deferral is for another operation.
                if occurrence not in deferred_occurrences:
                    raise RuntimeError(
                        f"ExistsAndEq source site unexpectedly lacks replay/deferred status: {module}:{occurrence}"
                    )
                exists_accepted_untargeted += sum(
                    int(stats["candidates"]) for stats in values
                )

        exists_source_sites.update(module_sites)
        exists_phase_counts.update(module_phases)
        all_recording_executions = sum(len(executions) for executions in outcomes.values())
        # Compute source-occurrence-level deferred Exists calls without relying
        # on the aggregate counter, which spans all modules.
        module_exists_deferred = 0
        for occurrence, values in cert_stats.items():
            if occurrence in deferred_occurrences:
                module_exists_deferred += sum(
                    int(stats["observations"]) for stats in values
                )
        module_result = (
            len(known),
            len(complete_occurrences),
            len(deferred_occurrences),
            sum(unsuccessful.values()),
            len(targeted_occurrences),
            targeted_replay_executions,
            exists_results,
            exists_candidates,
            module_exists_deferred,
        )
        module_results[module] = module_result
        aggregate.update(
            {
                "occurrences": len(known),
                "completeOccurrences": len(complete_occurrences),
                "deferredOccurrences": len(deferred_occurrences),
                "unsuccessful": sum(unsuccessful.values()),
                "recordingExecutions": all_recording_executions,
                "targetedMaterializedOccurrences": len(targeted_occurrences),
                "targetedReplayExecutions": targeted_replay_executions,
                "existsCommittedResults": exists_results,
                "existsSemanticCandidates": exists_candidates,
                "existsUnsupportedResults": exists_unsupported,
                "existsResultsInDeferredOccurrences": module_exists_deferred,
                "existsSourceSites": len(module_sites),
            }
        )
        print(
            f"SIMP_ENGINE_EXISTS_SOURCE_PROGRESS {index}/65 "
            f"module={module} occurrences={len(known)} complete={len(complete_occurrences)} "
            f"deferred={len(deferred_occurrences)} targetedMaterialized={len(targeted_occurrences)} "
            f"targetedReplay={targeted_replay_executions} exists={exists_results} "
            f"elapsed={time.monotonic()-started:.1f}s",
            flush=True,
        )

    aggregate["existsAuthorized"] = exists_authorized
    aggregate["existsAcceptedUntargeted"] = exists_accepted_untargeted
    strict_exists_totals = {"existsCommittedResults": 94}
    for field, expected in strict_exists_totals.items():
        if aggregate[field] != expected:
            raise RuntimeError(
                f"ExistsAndEq aggregate accounting changed: {field}="
                f"{aggregate[field]}, expected {expected}; aggregate={dict(aggregate)}"
            )
    if aggregate["existsSemanticCandidates"] + aggregate["existsUnsupportedResults"] != \
            aggregate["existsCommittedResults"]:
        raise RuntimeError(
            "ExistsAndEq support classification does not partition "
            f"committed results: aggregate={dict(aggregate)}"
        )
    if aggregate["existsAcceptedUntargeted"] + aggregate["existsAuthorized"] != \
            aggregate["existsSemanticCandidates"]:
        raise RuntimeError(
            "ExistsAndEq authorization classification does not partition accepted candidates: "
            f"aggregate={dict(aggregate)}"
        )
    if exists_phase_counts != Counter({"pre": 93, "post": 1}):
        raise RuntimeError(f"ExistsAndEq phase accounting changed: {dict(exists_phase_counts)}")
    if len(exists_source_sites) != 77:
        raise RuntimeError(f"ExistsAndEq source-site total changed: {len(exists_source_sites)}")

    expected_modules = {module: list(values) for module, values in EXPECTED_MODULE_TOTALS.items()}
    actual_modules = {module: list(values) for module, values in module_results.items()}
    if not unlocked:
        if dict(aggregate) != EXPECTED_TOTALS:
            raise RuntimeError(
                f"targeted ExistsAndEq source totals changed: expected {EXPECTED_TOTALS}, "
                f"got {dict(aggregate)}"
            )
        if actual_modules != expected_modules:
            raise RuntimeError(
                "targeted ExistsAndEq source module totals changed: "
                f"expected {expected_modules}, got {actual_modules}"
            )
    else:
        print(f"SIMP_ENGINE_EXISTS_SOURCE_CURRENT totals={dict(aggregate)}", flush=True)
        print(f"SIMP_ENGINE_EXISTS_SOURCE_CURRENT modules={actual_modules}", flush=True)

    modules = ",".join(sorted(module_results))
    print(
        "ExistsAndEq targeted source: "
        f"modules={modules} occurrences={aggregate['occurrences']} "
        f"completeOccurrences={aggregate['completeOccurrences']} "
        f"deferredOccurrences={aggregate['deferredOccurrences']} "
        f"targetedMaterializedOccurrences={aggregate['targetedMaterializedOccurrences']} "
        f"recordingExecutions={aggregate['recordingExecutions']} "
        f"targetedReplayExecutions={aggregate['targetedReplayExecutions']} "
        f"existsCommittedResults={aggregate['existsCommittedResults']} "
        f"existsSemanticCandidates={aggregate['existsSemanticCandidates']} "
        f"existsUnsupportedResults={aggregate['existsUnsupportedResults']} "
        f"existsAcceptedUntargeted={aggregate['existsAcceptedUntargeted']} "
        f"existsResultsInDeferredOccurrences={aggregate['existsResultsInDeferredOccurrences']} "
        f"existsAuthorized={aggregate['existsAuthorized']} "
        f"existsSourceSites={len(exists_source_sites)}: ok"
    )


if __name__ == "__main__":
    main()
