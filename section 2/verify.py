#!/usr/bin/env python3
"""Build the project and audit every public §2 theorem plus selected reuse."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import importlib.util
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
SCRATCH = SECTION / ".scratch"
RECORD = SECTION / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REUSE = [
    "SpecialTransformations.Section3.Balls.rvFibre_zero",
    "SpecialTransformations.Section3.Balls.rvFibre_eq_openDisc",
    "SpecialTransformations.Section3.BallImaginaries.lemma_3_13",
    "SpecialTransformations.Section3.lemma_3_3",
    "SpecialTransformations.Section3.GammaParameters.c_minimal_gamma_base",
    "SpecialTransformations.Section7.valuationRing_henselian",
    "IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub",
    "SpecialTransformations.Section3.canonical_algebraicClosureSubstructure_elementary",
    "SpecialTransformations.Section6.HenselianTheory.henselian_of_compatible_equiv",
    "SpecialTransformations.Section6.henselian_automorphism_invariance",
    "SpecialTransformations.Section6.lemma_6_2_in_algebraic_envelope_pure",
    "SpecialTransformations.Section6.DclClosed.image",
    "SpecialTransformations.Section3.lemma_3_9",
    "SpecialTransformations.Section3.lemma_3_6_vf",
    "SpecialTransformations.Section3.GammaParameters.lemma_3_6_rv",
    "SpecialTransformations.Section3.RawClosure.finite_of_definable_subset_algebraic",
    "SpecialTransformations.Section3.Saturated.definable_finite_subcover",
    "SpecialTransformations.Section3.RawClosure.hasMore_definable",
    "SpecialTransformations.Section3.RawClosure.no_inj_iff_finite_ncard_le",
    "SpecialTransformations.Section3.DefinableAt.isBoolComb_balls",
    "SpecialTransformations.Section3.GammaParameters.algebraic_vf_iff_real",
    "SpecialTransformations.Section3.algebraicAt_vf_union_rv_iff",
    "SpecialTransformations.Section3.GammaParameters.promote_scalar_definable_base",
    "SpecialTransformations.Section3.GammaParameters.tuple_singleton_definable_base",
    "SpecialTransformations.Section4.exists_independent_of_contains_box",
    "SpecialTransformations.Section3.algebraicAt_vf_isAlgebraic",
    "SpecialTransformations.Section3.algebraicAt_vf_iff_parameterField",
    "SpecialTransformations.Section8.vfTupleValue_le_component",
    "SpecialTransformations.Section8.vfTupleValue_eq_component",
    "SpecialTransformations.Section8.vfTupleValue_zero",
    "SpecialTransformations.Section9.vfTupleValue_ne_zero",
    "SpecialTransformations.Section9.HasVFDerivativeAt.unique",
    "SpecialTransformations.Section9.HasVFDerivativeAt.hasPartialAt",
    "SpecialTransformations.Section8.rvFibre_locallyConstant_of_independent",
    "SpecialTransformations.Section8.lemma_8_9_canonical",
    "SpecialTransformations.Section8.rawOpenBall_infinite",
    "SpecialTransformations.Section8.infinite_definable_contains_small_ball",
    "SpecialTransformations.Section3.GammaParameters.gamma_definable_finite_thresholds",
    "SpecialTransformations.Section3.FiniteThresholds.exists_infimum",
    "SpecialTransformations.Section3.GammaParameters.leastCodes_definable_base",
    "SpecialTransformations.Section9.isVFLimitSet_iff",
    "SpecialTransformations.Section9.IsMinimalVFLimitSet.isolated",
    "SpecialTransformations.Section9.lemma_9_2_topological",
    "SpecialTransformations.Section4.lemma_4_3",
    "SpecialTransformations.Section4.vfDim_image_le",
    "SpecialTransformations.Section4.model_valuation_nontrivial",
    "SpecialTransformations.Section4.rawFixedRVFibre_sorted",
    "SpecialTransformations.Section4.independent_definable_mem_nhds",
    "SpecialTransformations.Section8.gamma_has_vf_representative",
    "SpecialTransformations.Section8.uniformBall_mem_nhds",
    "SpecialTransformations.Section8.exists_uniformBall_subset_of_mem_nhds",
    "SpecialTransformations.Section9.exists_pairwise_disjoint_limitBall",
    "SpecialTransformations.Section9.IsMinimalLimitSet.frequently_hits",
    "SpecialTransformations.Section9.lemma_9_5",
    "SpecialTransformations.Section9.vfClosure_eq_closure",
    "SpecialTransformations.Section9.lemma_9_4",
    "SpecialTransformations.Section8.normalize_eq_of_isCanonical",
    "SpecialTransformations.Section3.finite_rv_to_vf_tuple_relation_image",
    "SpecialTransformations.Section3.GammaParameters.EndpointLogic.codeValue_surjective",
    "closure_subtype",
    "isClosed_eq",
    "SpecialTransformations.Section8.lemma_8_7_canonical",
    "SpecialTransformations.Section4.vfDim_eq_arity_of_contains_polydisc",
    "SpecialTransformations.Section4.TupleFamilies.uniform_coding",
    "SpecialTransformations.Section8.continuousInputsFamily_definable",
    "SpecialTransformations.Section8.mem_continuousInputs_iff",
    "SpecialTransformations.Section8.rvConstantRaw_definable",
    "SpecialTransformations.Section8.continuousAt_of_independent",
    "SpecialTransformations.Section8.vfDim_lt_of_no_independent",
    "SpecialTransformations.Section9.HasMixedVFJacobianAt.unique",
    "SpecialTransformations.Section9.exists_totalMixedJacobianMap",
    "SpecialTransformations.Section9.mixedDifferentiableAt_of_independent",
    "SpecialTransformations.Section9.mixedDifferentiabilityLocus_definable",
    "SpecialTransformations.Section9.mixed_vfDim_lt_of_no_independent",
    "SpecialTransformations.Section9.HasVFDerivativeAt.maps_vfBall",
    "SpecialTransformations.Section3.GammaParameters.Relation.precomposeGamma",
    "SpecialTransformations.Section3.GammaParameters.Relation.imageReal",
    "SpecialTransformations.Section3.GammaParameters.Relation.inter",
    "SpecialTransformations.Section3.GammaParameters.Relation.interRealPreimage",
    "SpecialTransformations.Section3.GammaParameters.promote_gamma_relation",
    "SpecialTransformations.ModelTheory.promote_definable_tuple_fibre",
    "SpecialTransformations.Section3.RawClosure.Tuple.GoodRelation",
    "SpecialTransformations.Section3.RawClosure.Tuple.good_relation_of_algebraic",
    "SpecialTransformations.Section3.Saturated.definable_finite_subcover_tuple",
    "SpecialTransformations.Section3.GammaParameters.DefinableOverBase.eliminate_definable_params",
    "SpecialTransformations.Section3.GammaParameters.gamma_value_of_named_code",
    "SpecialTransformations.Section3.small_union_range",
    "SpecialTransformations.Section3.GammaParameters.proper_normalized_definable",
    "SpecialTransformations.Section3.GammaParameters.representatives_values",
    "SpecialTransformations.Section9.IsLimitSet.mem_of_frequently_hits",
    "SpecialTransformations.Milestone0.Transfer.vfInvFun",
    "Valued.isClopen_ball",
    "ContinuousInv₀.continuousAt_inv₀",
    "FirstOrder.Language.exists_elementarySubstructure_card_eq",
    "FirstOrder.Language.ElementarySubstructure.meetsDefinable",
    "SpecialTransformations.Section3.VFFieldBase.ofSubstructure",
    "SpecialTransformations.Section3.definableClosureAt_vf_inv",
    "VFAlgClosed.isAlgClosed_vfType",
    "Topology.IsOpenEmbedding.piMap",
    "Topology.IsEmbedding.closure_eq_preimage_closure_image",
    "Topology.IsEmbedding.prodMap",
    "Topology.IsClosedEmbedding.prodMap",
    "Topology.IsClosedEmbedding.isClosed_iff_image_isClosed",
    "SpecialTransformations.Section3.Values.vrv_le_iff",
    "SpecialTransformations.Section3.raw_definableOver_sorted",
    "SpecialTransformations.Section8.vfRawClosure_definable",
    "SpecialTransformations.Section8.mem_vfRawClosure_iff",
    "Homeomorph.image_closure",
    "Homeomorph.image",
    "SpecialTransformations.Section8.uniformBallRelation_definable",
    "IsOpenMap.preimage_closure_eq_closure_preimage",
    "SpecialTransformations.Section8.unary_graph_polynomial_relation",
    "SpecialTransformations.Section8.mvPolynomial_has_shape",
    "SpecialTransformations.Section8.scalar_eventually_zero_or_positive_power",
    "SpecialTransformations.Section8.exists_gammaPowerGerm",
    "SpecialTransformations.Section8.unary_definable_punctured_germ",
    "SpecialTransformations.Section3.Values.gamma_pow_surjective",
    "SpecialTransformations.Section3.GammaParameters.finite_image_of_definable_cuts",
    "SpecialTransformations.Section4.GammaSyntax.mul_definable",
    "SpecialTransformations.Section4.GammaSyntax.one_definable",
    "SpecialTransformations.Section5.contractionMap",
    "SpecialTransformations.Section5.contractionFun_spec",
    "SpecialTransformations.Section5.contractionFun_unique",
    "SpecialTransformations.Section9.rvGammaJacobian_comp",
]
DEFINITIONS = [
    "VF", "RVInfinity", "rvZero", "RV", "GammaInfinity", "Gamma",
    "ParameterBase", "DclVFGenerated", "DclVFGammaGenerated", "DefinableOverBase",
    "VFGenerated", "VFGeneratedFieldBase",
    "Mixed", "rvCoordinates", "rvHull", "IsRVPullback", "rvBoundary",
    "DC", "closedDiscCode", "openDiscCode", "GraphFibreContinuous",
    "finiteValue", "labelledComp", "r023_f", "r023_g",
    "nonzeroRVCode",
    "HasVFInteriorDim", "vfDimension", "rvInputValues", "rvTargetValues",
    "rvMapGraph", "RVHasFiniteMap", "rvDimension",
    "ClosedDC", "ClosedDiscDefinable", "ClosedDiscAlgebraic",
    "GeneratesCompleteType", "IsCompleteTypeDefinable", "IsAtomic", "adjoinGamma",
    "NontrivialDefinableGamma", "AtomicGammaBaseChangeInput", "DiscAlgebraic", "DiscDefinable",
    "adjoinRV",
    "finitePolydiscNames", "FinitePolydiscRelation", "FinitePolydiscRelation.fibre",
    "AlgebraicOverFinitePolydiscNames",
    "vfRVImage",
    "IsOpenDisc", "IsClosedDisc", "thinAnnulus", "IsThinAnnulus", "IsPrimitiveDisc",
    "scalarVFGraph",
    "PrimitiveImageInput", "OpenDiscImageInput",
    "vfFunctionGraph", "vfRelationTags", "vfTagBranch",
    "tupleBase", "coordinateLineImage",
    "FiniteDiscTupleRelation", "FiniteDiscTupleRelation.fibre",
    "DefinableOverFiniteDiscNames", "GeneratesTypeOverFiniteDiscNames",
    "IsAtomicOverFiniteDiscNames",
    "scalarRVBoundary", "scalarBoundaryTuples", "vfCoordinateSection",
    "coordinateValues", "tupleValue", "HasDerivativeAt", "HasPartialDerivativeAt",
    "rvFunctionGraph", "RVFunctionLocallyConstantAt",
    "FinitePolydiscRelation.toTuple", "FiniteDiscTupleRelation.toScalar",
    "ValuedCoordinates", "valuationCoordinates", "valim",
    "GammaBoundedBy", "GammaDoublyBoundedBy", "BoundedBy", "DoublyBoundedBy",
    "IsBounded", "IsDoublyBounded",
    "HasLimitSet", "HasMinimalLimitSet", "BoundedVFRange",
    "forgetRVCoordinatesMap",
    "IsOpenDiscPartition",
    "gammaIndexedFamilyGraph",
    "fibreClosure", "fibreOpenExtension", "fibreGraph",
    "vfCorrespondenceGraph", "FinitaryRVCode",
    "FinitaryRVCode.labelGraph", "FinitaryRVCode.typedCode",
    "FinitaryRVCode.codedGraph", "FinitaryRVCode.branchDomain",
    "FinitaryRVCode.branchGraph", "FinitaryRVCode.HasValue",
    "FinitaryRVCode.branch", "FinitaryRVCode.branchBadRaw", "FinitaryRVCode.badRaw",
    "repeatVFMap", "jacobianFibre",
    "FiniteDiscTupleRelation.imageReal", "FiniteDiscTupleRelation.inter",
    "FiniteDiscTupleRelation.pullbackDiscNames", "gammaRelationPreimageMap",
    "UnaryDiscAtomicityInput", "AtomicDiscGammaBaseChangeInput",
    "coordinateDiscBase", "FiniteDiscTupleRelation.coordinateLine", "namedPolydisc",
    "singletonDiscTupleNames", "SingletonDiscTupleRelation", "SingletonDiscTupleRelation.fibre",
    "DefinableOverSingletonDiscNames", "namedSingletonPolydisc", "IsAtomicOverSingletonDiscNames",
    "FiniteDiscTupleRelation.fixPrefix", "normalFormDiscNames", "prefixedNamedPolydisc",
    "IsAtomicOverDiscNamesNormalForm", "PolydiscNaming", "discNameProduct",
    "finitePolydiscNaming", "DefinableOverPolydiscNames", "IsAtomicOverPolydiscNames",
    "FiniteChoice.RelationDefinable", "FiniteChoice.GoodRelation", "rawVFRelation",
    "vfApproach", "avoidFiniteVF", "curveSource",
    "invertCoordinates", "inversionDomain", "projectiveMask", "projectiveCentre",
    "projectiveClosure", "rawVFInverse", "rawInvertCoordinates", "projectiveParameters",
    "vfPullback", "elementaryVFGeneratedFieldBase", "vfInfinitySide", "vfEscape",
    "ProjectiveLine", "ProjectiveLine.finite", "ProjectiveLine.infinity",
    "ProjectiveLine.reciprocalChart", "ProjectiveLine.reciprocal", "ProjectiveLine.topology",
    "ProjectiveLine.reciprocalHomeomorph",
    "finiteProjectiveTuple", "projectiveTuple", "projectiveTupleChart", "projectiveChartBall",
    "projectiveGraph", "relativeProjectiveGraph", "ProjectiveGraphCluster",
    "projectiveTarget", "compactifiedTargetGraph", "affineTargetGraph",
    "vfGammaGraph", "partitionEscape",
    "mixedTuple", "mixedSort", "MixedDefinable", "mixedMapGraph", "MixedMapDefinable",
    "FibreConcentric", "HasDiscToDiscProperty", "DiscToDiscPartition", "DiscToDiscPartitionInput",
    "relativeBadLocus", "fibreBallHits", "rawGammaBallRelation", "radiusGoodFibre",
    "goodRadiusCodes", "goodRadiusProjection", "vfPairValues", "vfPairHomeomorph",
    "vfRawFibreClosure", "vfPairMapGraph", "relativePairProjectiveGraph",
    "affineFibreGraph", "reciprocalFibreGraph",
    "projectiveFibreGraph", "projectiveFibreChart",
    "rawTypeLocus",
    "containedFibreCodes",
    "rawOpenPolydiscProper",
    "rawOpenPolydisc",
    "rawPointImageCodes",
    "rawOpenImageCodes",
    "rawDiscShapeCodes",
    "rawTaggedPolydiscImage",
    "rawPolydiscTagRow",
    "rawGoodTaggedPolydiscCodes",
    "UnaryOpenDiscRVBaseChangeInput",
    "OpenDiscNamesImageInput",
    "openPolydiscCarrier",
    "openPolydiscGammaRelation",
    "TaggedPolydiscBranchDecomposition",
    "TaggedPolydiscBranchDecompositionOverDiscNames",
    "discCompactnessNames", "namedDiscTypeLocus", "badDiscFibreCodes",
    "FiniteDiscTupleRelation.rawOperation",
    "parametricTaggedImage", "parametricTagRow",
    "rvRawMapGraph",
    "rvCollapseZero",
    "rvCollapseTuple",
    "rvOne",
    "rvTupleProduct",
    "rvReindexed",
    "rawSingletonRows",
    "rawUniqueChoice",
    "firstChoiceDomain",
    "rvRawFibre",
    "rawCoordinateSection",
    "boundaryParameterSort",
    "boundaryFibreRelation",
    "coordinateBoundaryPairs",
    "boundaryTagSet",
    "boundaryRepresentativeCandidates",
    "boundaryRepresentativeValues",
    "ZeroFaceChart",
    "zeroFaceChart",
    "ZeroFaceChart.zeroIndex",
    "ZeroFaceChart.freeIndex",
    "ZeroFaceChart.insert",
    "ZeroFaceChart.project",
    "ZeroFaceChart.slice",
    "ZeroFaceChart.lift",
    "rawRVPolydisc",
    "OpenRVRowsConstant",
    "RVPolydiscRowsConstant",
    "rawCoordinateProjection",
    "rawRVValues",
    "rawVFComplement",
    "rawRVImage",
    "rawRVBoundary",
    "rawRVInterior",
    "lastToCoordinate",
    "rvCoordinateCylinder",
    "rawScalarCorrespondenceGraph",
    "boundaryRVGraph",
    "boundaryCoverPiece",
    "scalarPartialGraph",
    "scalarZeroExtension",
    "gammaPowerOrderIso",
    "gammaAffineRadius",
    "puncturedGammaDisc",
    "PuncturedValueLaw",
    "gammaPowerRelationImage",
    "GammaPiecewiseRationalAffineInput",
    "rawFibreForallCompare",
    "rawGammaFamilyGraph",
    "mixedGammaGraph", "mixedGammaFamily", "IsMixedOpenDiscPartition",
    "DefinableOverDiscGroundAndPolydiscNames",
    "IsAtomicOverDiscGroundAndPolydiscNames",
    "FiniteDiscTupleRelation.preimageRealMap",
    "prefixedCoordinateGammaIndex",
    "prefixedCoordinateRealMap",
    "prefixedCoordinateRelation",
    "FiniteDiscTupleRelation.prefixedCoordinateLine",
    "IsContractibleAlong",
    "contractionAlong",
    "IsRVContractible",
    "rvContraction",
    "definableRVContraction",
    "GammaLabels",
    "rvFiniteValue",
    "gammaLabelWeight",
    "gammaJacobian",
    "finiteDiscRawProper",
    "finiteDiscRawMember",
    "finiteDiscRawCentres",
    "finiteDiscRawNames",
    "finiteDiscRawEq",
    "discHullCurrent",
    "discHullArguments",
    "discInvariantHull",
    "discPromotedGammaRelation",
    "FiniteDiscTupleRelation.promoted",
    "rawGammaUpperGraph",
    "rawGammaLUBGraph",
    "rawGammaLessGraph",
    "rawFibreRelationalImage",
    "gammaAbs",
    "gammaAbsCodeRelation",
    "projectedGammaFamily",
    "gammaDomainCodes",
    "rvValueDomain",
    "rvValueFamily",
    "rvValueSource",
    "rawHeadDomain",
    "RVCodeDoublyBounded",
    "RVValueDoublyBounded",
    "rvGammaFunctionGraph",
    "rvGammaRawExtension",
    "rvScalarFunctionGraph",
]


def run(args: list[str], log: Path) -> str:
    with log.open("w") as output:
        result = subprocess.run(args, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    text = log.read_text()
    if result.returncode:
        raise SystemExit(f"FAIL ({result.returncode}): {' '.join(args)}; see {log}")
    return text


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    SCRATCH.mkdir(exist_ok=True)
    RECORD.mkdir(exist_ok=True)
    spec = importlib.util.spec_from_file_location("prepare_reuse", SECTION / "prepare-reuse.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    reuse_manifest = module.prepare()
    integration_spec = importlib.util.spec_from_file_location(
        "prepare_integration_reuse", ROOT / "section 3/prepare-integration-reuse.py")
    integration_module = importlib.util.module_from_spec(integration_spec)
    integration_spec.loader.exec_module(integration_module)
    integration_patch = integration_module.prepare()
    sources = sorted(SECTION.glob("*.lean"))
    exports: list[str] = []
    for source in sources:
        text = source.read_text()
        if re.search(r"\b(sorry|admit|axiom)\b", text):
            raise SystemExit(f"FAIL: proof placeholder or custom axiom in {source}")
        # Track top-level namespaces as well as sections: new coding modules
        # keep their branch theorems in the FinitaryRVCode namespace.
        scopes: list[tuple[str, str]] = []
        for line in text.splitlines():
            scope = re.fullmatch(r"(namespace|section)(?:\s+([\w.]+))?\s*", line)
            if scope:
                scopes.append((scope[1], scope[2] or ""))
                continue
            if re.fullmatch(r"end(?:\s+[\w.]+)?\s*", line):
                if not scopes:
                    raise SystemExit(f"FAIL: unmatched top-level end in {source}")
                scopes.pop()
                continue
            theorem = re.match(r"^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)", line)
            if theorem:
                prefix = ".".join(name for kind, name in scopes if kind == "namespace")
                if not prefix.startswith("DiamondIntegral.Section2"):
                    raise SystemExit(f"FAIL: unexpected theorem namespace in {source}: {prefix}")
                exports.append(prefix + "." + theorem[1])
        if scopes:
            raise SystemExit(f"FAIL: unclosed top-level scope in {source}")
    if not exports or len(set(exports)) != len(exports):
        raise SystemExit("FAIL: empty or duplicate public theorem inventory")

    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    if not version.startswith("Lean (version 4.35.0,"):
        raise SystemExit(f"FAIL: unexpected toolchain: {version}")
    pins = {
        "mathlib": "56a005855ea17e0b0958f73ec801ae140b0a1679",
        "acvf_qe": "939346b0a99899e22a873479364e3cc5d142731c",
        "special_transformations": "9cc9760892092dd34cfad4a6dee655843c52f30c",
        "integration_in_acvf": "7d4acc730496b3bd05a22c268ffd89540ca694f9",
    }
    for package, expected in pins.items():
        actual = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT / ".lake/packages" / package, text=True
        ).strip()
        if actual != expected:
            raise SystemExit(f"FAIL: {package} revision {actual} != {expected}")

    run(["lake", "-R", "build", "DiamondIntegral", "Section3.Library", "Section4.PolydiscLocal", "Section5.Library"], SCRATCH / "build.log")
    audit = [
        "import DiamondIntegral",
        "import Section3.Library",
        "import Section3.VFAlgebraicity",
        "import Section3.GammaBaseCMinimal",
        "import Section5.Library",
        "import Section4.PolydiscLocal",
        "set_option pp.universes true",
        "set_option pp.fullNames true",
        "set_option format.width 120",
    ]
    audit += [f"#print DiamondIntegral.Section2.{name}" for name in DEFINITIONS]
    library_headlines = json.loads((SECTION / "reuse/headlines.json").read_text())
    reuse_theorems = list(dict.fromkeys(REUSE + library_headlines))
    audit += ["#print SpecialTransformations.Section3.Balls.OpenRadius",
              "#print SpecialTransformations.Section3.Balls.openDisc",
              "#print SpecialTransformations.Section3.Balls.closedDisc",
              "#print SpecialTransformations.Section8.vfTupleValue",
              "#print SpecialTransformations.Section9.HasVFDerivativeAt",
              "#print SpecialTransformations.Section9.HasVFPartialAt",
              "#print SpecialTransformations.Section9.IsVFChartAt",
              "#print SpecialTransformations.Section9.HasMixedVFDerivativeAt",
              "#print SpecialTransformations.Section9.HasMixedVFJacobianAt",
              "#print SpecialTransformations.Section9.LimitPoint",
              "#print SpecialTransformations.Section9.memLimitBall",
              "#print SpecialTransformations.Section9.IsLimitSet",
              "#print SpecialTransformations.Section9.IsMinimalLimitSet",
              "#print SpecialTransformations.Section9.unaryLimitGraph",
              "#print SpecialTransformations.Section9.LimitSetDefinable"]
    for name in exports + reuse_theorems:
        audit += [f"#check @{name}", f"#print axioms {name}"]
    audit_file = SCRATCH / "Audit.lean"
    audit_file.write_text("\n".join(audit) + "\n")
    output = run(["lake", "env", "lean", str(audit_file)], SCRATCH / "audit.log")
    audited: dict[str, list[str]] = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        # Lean sometimes prints the core alias `choice` for Classical.choice.
        raw = re.sub(r"\.\{[^}]*\}", "", raw)
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        axioms = {"Classical.choice" if a == "choice" else a for a in axioms}
        if not axioms <= ALLOWED:
            raise SystemExit(f"FAIL: {name} has disallowed axioms {axioms - ALLOWED}")
        audited[name] = sorted(axioms)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        audited[name] = []
    missing = set(exports + reuse_theorems) - audited.keys()
    if missing:
        raise SystemExit(f"FAIL: missing axiom audits: {sorted(missing)}")
    if "sorryAx" in output or "error:" in output:
        raise SystemExit("FAIL: audit output contains an error or proof placeholder")

    inputs = sources + [ROOT / name for name in ("DiamondIntegral.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "ACCEPTED-CITED-RESULTS.md")]
    inputs += [SECTION / name for name in ("verify.py", "prepare-reuse.py", "reuse/manifest.json", "reuse/headlines.json", "reuse/open-disc-radius.patch")]
    inputs += [ROOT / "section 3" / name for name in (
        "prepare-integration-reuse.py", "reuse/integration-manifest.json", "reuse/integration-open-radius.patch")]
    inputs += [RECORD / "CITED-INPUTS.md", RECORD / "DISC-GROUND-REVIEW.md", RECORD / "UPSTREAM-LINKS.md", RECORD / "UPSTREAM-LINKS.json"]
    record = {
        "status": "PASS",
        "scope": "Project build; public section theorem types/axioms; selected reuse types/axioms. Semantic scope review: COVERAGE.md, STATUS.md and verification/DISC-GROUND-REVIEW.md.",
        "lean": version,
        "pins": pins,
        "approved_library_patch": reuse_manifest,
        "integration_compatibility_patch": integration_patch,
        "checked_cited_adapters": {
            "AtomicGammaBaseChangeInput": "DiamondIntegral.Section3.integrationAtomicGammaBaseChangeInput_complete (requires ACVF00)",
            "PrimitiveImageInput": "DiamondIntegral.Section3.integrationPrimitiveImageInput",
            "OpenDiscImageInput": "DiamondIntegral.Section3.integrationOpenDiscImageInput",
            "AtomicDiscGammaBaseChangeInput": "DiamondIntegral.Section3.integrationAtomicDiscGammaBaseChangeInput",
            "UnaryDiscAtomicityInput": "DiamondIntegral.Section3.integrationUnaryDiscAtomicityInput (requires actual saturation at an infinite cardinal)",
            "UnaryOpenDiscRVBaseChangeInput": "DiamondIntegral.Section3.integrationUnaryOpenDiscRVBaseChangeInput",
            "OpenDiscNamesImageInput": "DiamondIntegral.Section3.integrationOpenDiscNamesImageInput",
            "DiscToDiscPartitionInput": "DiamondIntegral.Section3.integrationDiscToDiscPartitionInput (requires actual saturation at an infinite cardinal)",
            "verification": "section 3/verification/VERIFICATION.json",
        },
        "sources": {str(p.relative_to(ROOT)): sha256(p) for p in inputs},
        "manuscript_sha256": sha256(SECTION / "reference/diamond_integral_revision_annotated.tex"),
        "accepted_cited_inputs": [{
            "interface": "DiamondIntegral.Section2.AtomicGammaBaseChangeInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.3",
            "used_by": ["DiamondIntegral.Section2.lemma_2_23"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.PrimitiveImageInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.8 (geometric conclusion)",
            "used_by": ["DiamondIntegral.Section2.lemma_2_27"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.OpenDiscImageInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.13 (nonconstant geometric conclusion)",
            "used_by": ["DiamondIntegral.Section2.lemma_2_28",
                        "DiamondIntegral.Section2.atomic_open_polydisc_image",
                        "DiamondIntegral.Section2.lemma_2_29"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.UnaryDiscAtomicityInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.4; Section 3 ball-imaginary context",
            "used_by": ["DiamondIntegral.Section2.lemma_2_25_unary",
                        "DiamondIntegral.Section2.namedPolydisc_definable_of_type",
                        "DiamondIntegral.Section2.lemma_2_25_finite_names",
                        "DiamondIntegral.Section2.lemma_2_25_singleton_normal_form",
                        "DiamondIntegral.Section2.lemma_2_25",
                        "DiamondIntegral.Section2.lemma_2_25_closed",
                        "DiamondIntegral.Section2.lemma_2_25_open",
                        "DiamondIntegral.Section2.lemma_2_25_with_disc_ground",
                        "DiamondIntegral.Section2.lemma_2_25_disc_ground_closed",
                        "DiamondIntegral.Section2.lemma_2_25_disc_ground_open",
                        "DiamondIntegral.Section2.corollary_2_30_disc_names"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.AtomicDiscGammaBaseChangeInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.3; Section 3 ball-imaginary context",
            "used_by": ["DiamondIntegral.Section2.lemma_2_23_disc_names",
                        "DiamondIntegral.Section2.lemma_2_23_disc_gamma_tuple",
                        "DiamondIntegral.Section2.lemma_2_25_finite_names",
                        "DiamondIntegral.Section2.lemma_2_25_singleton_normal_form",
                        "DiamondIntegral.Section2.lemma_2_25",
                        "DiamondIntegral.Section2.lemma_2_25_closed",
                        "DiamondIntegral.Section2.lemma_2_25_open",
                        "DiamondIntegral.Section2.lemma_2_25_with_disc_ground",
                        "DiamondIntegral.Section2.lemma_2_25_disc_ground_closed",
                        "DiamondIntegral.Section2.lemma_2_25_disc_ground_open",
                        "DiamondIntegral.Section2.corollary_2_30_disc_names"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.DiscToDiscPartitionInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Proposition 3.19 and mixed-coordinate Proposition 3.21",
            "used_by": ["DiamondIntegral.Section2.lemma_2_32"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.UnaryOpenDiscRVBaseChangeInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.9 (atomicity formulation of set-valued RV constancy); Section 3 ball-imaginary context",
            "used_by": ["DiamondIntegral.Section2.named_open_disc_rv_rows_constant",
                        "DiamondIntegral.Section2.lemma_2_24_disc_names",
                        "DiamondIntegral.Section2.lemma_2_26_disc_names",
                        "DiamondIntegral.Section2.type_polydisc_rv_rows_constant",
                        "DiamondIntegral.Section2.type_polydisc_tagged_branch_image",
                        "DiamondIntegral.Section2.corollary_2_30",
                        "DiamondIntegral.Section2.lemma_2_29_disc_names",
                        "DiamondIntegral.Section2.corollary_2_30_disc_names"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.OpenDiscNamesImageInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, Lemma 3.13 (unary nonconstant geometric conclusion); Section 3 ball-imaginary context",
            "used_by": ["DiamondIntegral.Section2.named_open_disc_image",
                        "DiamondIntegral.Section2.type_polydisc_tagged_branch_image",
                        "DiamondIntegral.Section2.corollary_2_30",
                        "DiamondIntegral.Section2.lemma_2_29_disc_names",
                        "DiamondIntegral.Section2.corollary_2_30_disc_names"],
            "status": "Legacy replaceable interface; checked constructor from pinned [18] now supplied in section 3. See checked_cited_adapters and the complete section 3 audit.",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }, {
            "interface": "DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput",
            "source": "Bibliography [18], Yin, Integration in algebraically closed valued fields, proof of Lemma 3.18: quantifier elimination and piecewise rational-affine Gamma functions",
            "used_by": ["DiamondIntegral.Section2.gamma_definable_image_doubly_bounded",
                        "DiamondIntegral.Section2.unary_rv_gamma_image_doubly_bounded",
                        "DiamondIntegral.Section2.lemma_2_41_gamma_raw",
                        "DiamondIntegral.Section2.lemma_2_41_gamma",
                        "DiamondIntegral.Section2.lemma_2_41"],
            "status": "Explicit author-accepted background from the context of [18, Section 3]; full guarded Gamma-code graph, characteristic zero and nontrivial ground Gamma retained; finite power-law boundedness proved here, full RV-domain 2.41 not assumed",
            "scope_record": "section 2/verification/CITED-INPUTS.md",
        }],
        "public_theorems": exports,
        "reuse_theorems": reuse_theorems,
        "axioms": {name: audited[name] for name in exports + reuse_theorems},
    }
    upstream_links = json.loads((RECORD / "UPSTREAM-LINKS.json").read_text())
    for entry in record["accepted_cited_inputs"]:
        entry["upstream_reference"] = upstream_links[entry["interface"].rsplit(".", 1)[-1]]
    (RECORD / "Audit.lean").write_text(audit_file.read_text())
    (RECORD / "headline-audit.txt").write_text(output)
    (RECORD / "status.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: project build, {len(exports)} public theorem audits, {len(reuse_theorems)} reuse audits")


if __name__ == "__main__":
    main()
