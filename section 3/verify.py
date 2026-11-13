#!/usr/bin/env python3
"""Build section 3 in the pinned project and audit its actual public exports."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
SCRATCH = SECTION / ".scratch"
RECORD = SECTION / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PINS = {
    "integration_in_acvf": "7d4acc730496b3bd05a22c268ffd89540ca694f9",
    "mathlib": "56a005855ea17e0b0958f73ec801ae140b0a1679",
    "acvf_qe": "939346b0a99899e22a873479364e3cc5d142731c",
    "special_transformations": "9cc9760892092dd34cfad4a6dee655843c52f30c",
}
REUSE = [
    "SpecialTransformations.Section4.PositiveAdditiveGrothendieck.universalEquiv",
    "Algebra.GrothendieckAddGroup.lift_apply_of",
    "Algebra.GrothendieckAddGroup.liftRingHom",
    "SpecialTransformations.DefinableGeometry.Map.inverse",
    "SpecialTransformations.Section4.rvLift_finite_rv_fibres",
    "DiamondIntegral.Section2.gammaJacobian_comp",
    "DiamondIntegral.Section2.vfDimension_eq_bot_iff",
    "AddCon.quotientKerEquivOfSurjective",
]
GROUPOID_INSTANCES = [
    "DiamondIntegral.Section3.PositiveMeasuredVF.positiveMeasuredVFGroupoid",
    "DiamondIntegral.Section3.instGroupoidZeroMeasuredVF",
    "DiamondIntegral.Section3.gammaObjectGroupoid",
    "DiamondIntegral.Section3.measuredGammaGroupoid",
    "DiamondIntegral.Section3.measuredVFObjectGroupoid",
    "DiamondIntegral.Section3.instGroupoidRVObject",
    "DiamondIntegral.Section3.instGroupoidVFObject",
    "DiamondIntegral.Section3.instGroupoidMeasuredRVObject",
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args: list[str], log: Path) -> str:
    with log.open("w") as output:
        result = subprocess.run(args, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"FAIL ({result.returncode}): {args}; see {log}")
    return log.read_text()


def main() -> None:
    SCRATCH.mkdir(exist_ok=True)
    RECORD.mkdir(exist_ok=True)
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    if not version.startswith("Lean (version 4.35.0,"):
        raise SystemExit(f"FAIL: unexpected toolchain {version}")
    for package, expected in PINS.items():
        actual = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT / ".lake/packages" / package, text=True
        ).strip()
        if actual != expected:
            raise SystemExit(f"FAIL: {package} revision {actual} != {expected}")
    spec = importlib.util.spec_from_file_location("prepare_reuse", ROOT / "section 2/prepare-reuse.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    patch = module.prepare()
    integration_spec = importlib.util.spec_from_file_location(
        "prepare_integration_reuse", SECTION / "prepare-integration-reuse.py")
    integration_module = importlib.util.module_from_spec(integration_spec)
    integration_spec.loader.exec_module(integration_module)
    integration_patch = integration_module.prepare()

    sources = sorted(SECTION.glob("*.lean"))
    tracked = sources + [SECTION / name for name in (
        "verify.py", "prepare-integration-reuse.py", "reuse/integration-manifest.json",
        "reuse/integration-open-radius.patch", "verification/integration-reuse.json", "verification/cited-inputs.json",
        "verification/paper-targets.json")]
    tracked += [ROOT / p for p in ("DiamondIntegral.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "ACCEPTED-CITED-RESULTS.md")]
    source_snapshot = {str(p.relative_to(ROOT)): sha(p) for p in tracked}
    exports = []
    definitions = []
    instances = set(GROUPOID_INSTANCES)
    for path in sources:
        source = path.read_text()
        if re.search(r"\b(sorry|admit|axiom)\b", source):
            raise SystemExit(f"FAIL: placeholder or custom logical premise in {path}")
        scopes = []
        for line in source.splitlines():
            scope = re.fullmatch(r"(?:noncomputable\s+)?(namespace|section)(?:\s+([\w.]+))?\s*", line)
            if scope:
                scopes.append((scope[1], scope[2] or ""))
                continue
            if re.fullmatch(r"end(?:\s+[\w.]+)?\s*", line):
                if not scopes:
                    raise SystemExit(f"FAIL: unmatched scope in {path}")
                scopes.pop()
                continue
            decl = re.match(
                r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|def|structure|abbrev)\s+([\w.]+)", line
            )
            instance_decl = re.match(r"^(?:(?:noncomputable|local)\s+)*instance\s+([\w.]+)", line)
            if instance_decl:
                prefix = ".".join(name for kind, name in scopes if kind == "namespace")
                if not prefix.startswith("DiamondIntegral.Section3"):
                    raise SystemExit(f"FAIL: unexpected instance namespace {prefix}")
                instances.add(prefix + "." + instance_decl[1])
            if decl:
                prefix = ".".join(name for kind, name in scopes if kind == "namespace")
                if not prefix.startswith("DiamondIntegral.Section3"):
                    raise SystemExit(f"FAIL: unexpected declaration namespace {prefix}")
                (exports if decl[1] == "theorem" else definitions).append(prefix + "." + decl[2])
        if any(kind == "namespace" or name for kind, name in scopes):
            raise SystemExit(f"FAIL: unclosed named scope in {path}")
    instances = sorted(instances)
    if not exports or len(exports) != len(set(exports)):
        raise SystemExit("FAIL: empty or duplicate theorem inventory")

    paper_targets = json.loads((RECORD / "paper-targets.json").read_text())
    target_heads = [name for target in paper_targets["targets"] for name in target["declarations"]]
    declared_heads = set(exports + definitions + instances + REUSE)
    integration_reuse = json.loads((RECORD / "integration-reuse.json").read_text())
    if integration_reuse["revision"] != PINS["integration_in_acvf"]:
        raise SystemExit("FAIL: integration export inventory revision differs from the dependency pin")
    linked_heads = [entry["consumer"] for entry in
                    integration_reuse["exports"] + integration_reuse.get("later_exports", [])]
    if set(linked_heads) - declared_heads:
        raise SystemExit(f"FAIL: missing integration proof exports: {sorted(set(linked_heads) - declared_heads)}")
    missing_target_heads = set(target_heads) - declared_heads
    if missing_target_heads or not paper_targets["targets"]:
        raise SystemExit(f"FAIL: manuscript target links missing: {sorted(missing_target_heads)}")
    if not paper_targets.get("no_HK_input"):
        raise SystemExit("FAIL: manuscript review must retain the no-HK-input boundary")

    run(["lake", "-R", "build", "DiamondIntegral"], SCRATCH / "build.log")
    audit = [
        "import DiamondIntegral",
        "set_option pp.universes true",
        "set_option pp.fullNames true",
        "set_option pp.notation false",
        "set_option format.width 120",
    ]
    audit += [f"#print {name}" for name in definitions + instances]
    for name in exports + definitions + instances + REUSE:
        audit += [f"#check @{name}", f"#print axioms {name}"]
    audit_file = SCRATCH / "Audit.lean"
    audit_file.write_text("\n".join(audit) + "\n")
    output = run(["lake", "env", "lean", str(audit_file)], SCRATCH / "audit.log")
    audited = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        raw = re.sub(r"\.\{[^}]*\}", "", raw)
        principles = {x.strip() for x in raw.split(",") if x.strip()}
        principles = {"Classical.choice" if x == "choice" else x for x in principles}
        if not principles <= ALLOWED:
            raise SystemExit(f"FAIL: disallowed principles in {name}: {principles - ALLOWED}")
        audited[name] = sorted(principles)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        audited[name] = []
    missing = set(exports + definitions + instances + REUSE) - audited.keys()
    if missing or "sorryAx" in output or "error:" in output:
        raise SystemExit(f"FAIL: incomplete audit: {sorted(missing)}")

    if sorted(SECTION.glob("*.lean")) != sources or any(
        sha(ROOT / path) != digest for path, digest in source_snapshot.items()
    ):
        raise SystemExit("FAIL: source changed during verification; rerun after edits finish")
    receipt = {
        "status": "PASS",
        "scope": "Project build, complete printed definitions/public theorem types and principle audit, with validated manuscript target links. Semantic completion is relative to the documented paper contexts and explicitly accepted cited inputs; see verification/paper-targets.json, STATUS.md and TARGETS.md.",
        "paper_target_review": {"status": paper_targets["status"], "targets": len(paper_targets["targets"]), "declaration_links": len(target_heads), "sha256": sha(RECORD / "paper-targets.json")},
        "lean": version,
        "pins": PINS,
        "approved_library_patch_sha256": patch["patch_sha256"],
        "source_sha256": source_snapshot,
        "integration_compatibility_patch": integration_patch,
        "integration_proof_exports": {"revision": integration_reuse["revision"], "declarations": len(linked_heads),
                                      "later_export_review": integration_reuse.get("later_export_review")},
        "manuscript_sha256": sha(ROOT / "section 2/reference/diamond_integral_revision_annotated.tex"),
        "audit_source_sha256": sha(audit_file),
        "audit_log_sha256": sha(SCRATCH / "audit.log"),
        "public_theorems": exports,
        "definitions_printed": definitions,
        "groupoid_instances": GROUPOID_INSTANCES,
        "typeclass_instances": instances,
        "reused_declarations": REUSE,
        "principles": audited,
        "conditional_scope": {
            "GammaCategoryInterpretation": "GammaHom and GammaGroundGammaHom use the intended full RV preimages, as clarified by the author. The lower map is well defined. C001's unnecessary definition correction is withdrawn; the partial-map alternative and its fifth-root example do not bear on the intended map or its monicity.",
            "integralFromKernel": "The generic integral construction requires the stated surjective lift and exact lift-kernel congruence. The later [18] VF integration kernels remain precise accepted inputs; the separate local tensor kernels are both proved here.",
            "no_definable_bijection_of_point_obstruction": "Requires one definable set to have a definable point and the other to have none. A particular model or base realizing the R053 example is not constructed by this lemma.",
            "VFObject": "Real-base and complete original-Gamma-ground VF objects use the actual section 2 intrinsic dimension and finite RV fibres. Applications must use the valuation topology. Independent disc names are outside this default context; already definable interpreted names eliminate without expanding the real base.",
            "positiveTensorPresentations": "Both elementary positive tensor congruences equal the actual kernels; both quotient semiring isomorphisms, direct-sum gradings and original object degrees are proved under the explicit canonical, ACVF00, saturation, small real/Gamma and nontrivial-Gamma hypotheses. TensorPresentationContext instantiates the actual VF/Gamma-generated context. No HK input or cancellation is used.",
            "groupifiedTensorPresentations": "Both actual groupified tensor kernels equal the ideals spanned by the differences of their explicit positive coefficient-translation pairs, in the tensor products over the actual finite-Gamma coefficient rings. Both quotient ring equivalences and original GammaGroundContext applications are proved. This is deduced from the exact positive presentations and the canonical completion/tensor equivalence, with no cancellation or embedding into group completion assumed. Evaluation descent to the actual RV rings is equivalent to equality on the displayed pairs, with existence, formulas and uniqueness checked. For every commuting presentation, the full annular pullback lands in the explicit unmeasured relation ideal. Concrete bounded section 4 comparison maps and the actual Euler evaluations remain separate section 4 constructions; no new cited input is introduced.",
            "coefficientSquareMonomorphisms": "Both ordinary horizontal positive coefficient maps are injective, on every homogeneous positive scissor monoid and on the graded positive semirings, under explicit canonical, ACVF00, uncountable saturation and small original real/Gamma ground hypotheses. GammaGroundCoefficientMonicityContext instantiates the manuscript VF/Gamma-generated context and discharges residue characteristic zero. The approved replaceable Reichstein--Youssin classification is the only additional cited input. All ACVF normalization, actual generic matching including finite tags and inverse compatibility, character symmetries, original-ground coefficient recovery, compactness and gluing to full bijective RV lifts are proved locally. The lower forward map is well defined from the full-preimage morphism definition without [19] or R--Y. The two vertical positive injections and the commuting square are proved. Later constructions require the horizontal homomorphisms and corrected kernel descent, not their injectivity. No groupified injection is inferred.",
            "GammaAffineClassification": "Both statements of Remark 3.15 now have local proofs over the complete original mixed ground, relative to the already approved R--Y classification: actual Gamma morphisms are exactly the finite branchwise piecewise unimodular maps with genuine definable RV translations; potentially nonbijective full-code contractions from Gamma^n to Gamma^m are piecewise integer-affine with rectangular integer matrices and genuine original-ground RV shifts. The latter stabilizes to the full RV shear (u,v)->(u,f(u)v) in degree n+m and restricts to the identity slice, including zero arities. GammaGroundContext wrappers discharge residue characteristic zero and retain all source and target data. The older [19] input is retained at its stated real VF-generated scope; it is not broadened or used for lower-map well-definedness.",
            "parameterTransport": "Already definable interpreted names add no sets or full map graphs over the complete Gamma ground. Finite VF and measured RV diagrams, including all labels, forms and arrows, have a common finite tuple of original Gamma names and reconstruct literally. Functors from one fixed finite-name stage are faithful; no fixed-stage fullness is claimed.",
            "degreeZeroVF_RV": "Both actual degree-zero category equivalences are proved over the complete original Gamma ground. Ordinary VF[0]/RV[0] uses invariant finite VF coding, ACVF00, saturation, small real base and the valuation topology. Measured degree zero retains all pointwise Gamma forms and needs no additional coding hypotheses.",
            "positiveEvaluationDescent": "An arbitrary commutative-semiring-valued evaluation descends exactly when it agrees on the elementary pairs. Balanced translation-invariant Gamma evaluations have a unique RV descent and retain the given RES coefficient map. Actual Euler-characteristic constructions and finite-coefficient balancing remain separate section 4 obligations. The positive tail absorption, concrete full-ring annulus vanishing, measured RV forgetful homomorphism, annihilation of the stipulated annular ideal and its pullback into the actual unmeasured tensor kernel for every commuting presentation are now proved. The concrete bounded section 4 categories and comparison maps are not yet constructed.",
        },
        "ci": "Local audit. GitHub Actions verification is reported separately after the author-authorized push.",
    }
    (RECORD / "Audit.lean").write_text(audit_file.read_text())
    (RECORD / "headline-audit.txt").write_text(output)
    (RECORD / "VERIFICATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {len(exports)} section theorem types; {len(REUSE)} reused declarations; standard principles only")


if __name__ == "__main__":
    main()
