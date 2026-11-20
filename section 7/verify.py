#!/usr/bin/env python3
"""Build Section 7 and audit complete public types and logical axioms."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
RECORD = SECTION / 'verification'
RECORD.mkdir(exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
sources = sorted(SECTION.glob('*.lean'))
declarations = []
for source in sources:
    body = source.read_text()
    stripped = re.sub(r'/\-.*?\-/', '', body, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    if re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b', stripped):
        raise SystemExit(f'FAIL: unproved or unsafe declaration in {source.name}')
    frames = []
    for line in stripped.splitlines():
        command = line.strip()
        opened = re.match(r'^namespace\s+([\w.]+)\s*$', command)
        section = re.match(r'^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$', command)
        closed = re.match(r'^end(?:\s+([\w.]+))?\s*$', command)
        if opened:
            frames.append(('namespace', opened.group(1)))
        elif section:
            frames.append(('section', section.group(1)))
        elif closed:
            if not frames:
                raise SystemExit(f'FAIL: unmatched end in {source.name}')
            kind, name = frames.pop()
            if closed.group(1) and closed.group(1) != name:
                raise SystemExit(f'FAIL: namespace/section mismatch in {source.name}: {closed.group(1)} / {name}')
        declaration = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|inductive)\s+([\w.']+)", command)
        if declaration:
            namespace = '.'.join(name for kind, name in frames if kind == 'namespace')
            if not (namespace.startswith('DiamondIntegral.Section7') or namespace.startswith('DiamondIntegral.Section6')):
                raise SystemExit(f'FAIL: declaration outside Sections 6-7 in {source.name}')
            declarations.append(namespace + '.' + declaration.group(1))
if len(declarations) != len(set(declarations)):
    raise SystemExit('FAIL: duplicate declaration in audit manifest')

subprocess.run(['lake', 'build', '«section 7».Section'], cwd=ROOT, check=True,
    stdout=(RECORD/'build.log').open('w'), stderr=subprocess.STDOUT)
audit = RECORD/'Audit.lean'
audit.write_text('import «section 7».Section\n\n' + '\n'.join(
    f'#check @{name}\n#print {name}\n#print axioms {name}' for name in declarations) + '\n')
checked = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=ROOT,
    check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout
(RECORD/'types-and-axioms.txt').write_text(checked)
axioms = re.findall(r"^'(.+)' depends on axioms: \[([^]]*)\]", checked, flags=re.M)
axioms += [(name, '') for name in re.findall(r"^'(.+)' does not depend on any axioms", checked, flags=re.M)]
if len(axioms) != len(declarations):
    raise SystemExit(f'FAIL: expected {len(declarations)} axiom records, got {len(axioms)}')
for name, names in axioms:
    actual = {n.strip() for n in names.split(',') if n.strip()}
    if actual - ALLOWED:
        raise SystemExit(f'FAIL: {name} uses {actual - ALLOWED}')
manifest = json.loads((ROOT/'lake-manifest.json').read_text())
status = {
    'status': 'PASS',
    'scope': 'Section 7 formalization in progress. Complete numbered results, on isomorphism classes of mu RV^db[1+k] over an arbitrary parameter base and with no input beyond the ACVF model: Definition 7.2 (elementary annular blowups with bounded variable apertures = Section 4 AnnularDatum/relative annular objects; restriction to definable pieces; blowups of length one and chains, on classes), Lemma 7.5 (BlowupResults.lemma_7_5), Corollary 7.6, Lemma 7.7, Corollary 7.8, Definition 7.9 (MuIsp) and the additive part of Lemma 7.10 (an AddCon); Lemma 7.12 on classes over the VF-generated base (BlowupLiftGeneral.lemma_7_12: liftCls [U^{tau,j}] = liftCls [U] for every aperture datum; step_lift, steps_lift, muIsp_lift for blowups of any length); Remark 7.3 (dimension claim); Definitions 7.16, 7.17, 7.19 and Remark 7.18 (infinity symmetry and slope); Corollary 6.37 on Section 7 classes (ChartOfMeasured.liftCls_surjective); Lemma 7.11 for the full lift, on classes over a substructure base ⟨T, ∅⟩ (SpecialChainInduction.lemma_7_11: along a relative aperture chain on the lift of a doubly bounded object, the contraction U_T has a class reached by blowups; relative_chain, special_chain, unary_chain); Lemma 7.13 in the printed form with head start 0 (KernelDimOne.lemma_7_13 for an isomorphism A = B in mu VF^diamond[1] and standard contractions; core lift_iso_muIsp; also over a substructure with support data, KernelBaseChange.lemma_7_13_of_support, e.g. the base adjoin T b with adjoined VF parameters). Remark 7.28 in all degrees (Remark728.remark_7_28, remark_7_28_zero; Section 3 ground context with strong homogeneity, Section 4 bounded RV decomposition). Lemma 7.14 (Lemma714Reduce.lemma714 : FiberwiseInput.Lemma714 M G, proved in the Lemma714* modules) and Lemma 7.20 (Lemma720.lemma720 M G : TwoCellInput.Lemma720 M G, proved in the Lemma720* modules). Corollary 7.15 (Corollary715Fibres.corollary_7_15; hypothesis-free form ProvedResults.corollary_7_15; centre independence, common centre, first stage and rest, fibre hypothesis at good points via slice morphisms and Lemma 7.13). Lemma 7.21 in the uniform form used by Lemma 7.22 (product cells: ProductCells.cls_product_orders; balanced cells: BalancedPiece.cls_balanced_orders, via the balanced translations, the matched chains of Lemma 6.38 and MapClasses.cls_labelObject_map), Lemma 7.22 on the object A* (Lemma723Two.lemma_7_22) and Lemma 7.23 for n = 2 (Lemma723TwoFinal.lemma_7_23_n2); hypothesis-free forms ProvedResults.lemma_7_22 and ProvedResults.lemma_7_23_n2 (formal reading of 7.22 in GAP-REPAIRS 14). Lemma 7.23 in every dimension (Lemma723General.lemma_7_23, hypothesis-free; Lemma723General.lemma_7_23_succ on the Lemma 7.14 input for n + 3 coordinates): reduction to the two-stage fibre hypothesis (Lemma723Reduction.reduction_7_23, grafting with head start k in HeadStartK), good points (FibreGood2), and at a good point the two slice contractions of the prepared slice in both orders compared by Lemma 7.23 for n = 2 over S<b> (SliceContractions.fibre_ispRel_at, TwoDimSlices, OrderedProgramContractions). Part (∗) of Proposition 7.24: independence of the contraction and its order (OrderIndependence.star, hypothesis-free; adjacent transpositions by Lemma 7.23, later positions by a common first stage (OrderGrafts, StageReindexing), tautological contractions of the lifted bundles (TautologicalContractions), Lemma 7.14 with one VF coordinate and the induction over S<a> on the fibres (FibreContractions, FirstStageObjects, StageBaseChange)). Proposition 7.24 in degree 0 (hypothesis-free) and, in degree n+1, on the temporary intermediate-forms input, which is false as stated (so not established) (Proposition724.proposition_7_24 and proposition_7_24_muIsp in degree n+1, hypothesis hIF only; Proposition724Zero.proposition_7_24_zero in degree 0, hypothesis-free): arrows of an isomorphism (MorphismClasses.morphism_classRel, Corollary715Moves.corollary_7_15_moves), scissor additivity (ScissorClasses), tautological contraction (TautologicalLifts), and the contraction class as an invariant of the scissor presentation of K_+ mu VF^diamond. Theorem 7.26: semigroup isomorphism (Proposition724.integralEquiv, Proposition724Zero.integralZero_bijective, with the characterization) and ring isomorphism K mu VF^diamond[*] = K mu RV^db[*]/J_var (Theorem726.integralRingEquiv, ring presentation DiamondRing, products of morphisms DiamondProducts). Remark 7.25: the kernel of the lift is J_var (Theorem726.remark_7_25; RingClasses.ispRel_mem). Corollary 7.27 on the classes of objects, input-free (Corollary727.corollary_7_27_left, corollary_7_27_right and the degree-0 forms; bottom-row ring maps bottomLeft, bottomRight). Supporting: the commutative monoid of isomorphism classes with refinement, and the mu VF^diamond chart lifts of Definitions 6.34-6.37.',
    'lean': subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip(),
    'repository_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'packages': {p['name']:p['rev'] for p in manifest['packages']},
    'declarations': declarations,
    'allowed_axioms': sorted(ALLOWED),
    'sources': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'verification_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'temporary_inputs': ['DiamondIntegral.Section7.IntermediateFormsInput.IntermediateForms M G (intermediate forms along a relatively unary factorization, for the arrows in the proof of Proposition 7.24; author decision of 2026-11-20, input + parallel build; GAP-REPAIRS 16). FALSE AS STATED for n = 2 (counterexample in its docstring); the results taking it are not established. Taken as the explicit hypothesis hIF by Proposition724, Theorem726 and MorphismClasses; unpacked only in UnaryArrows.'],
    'proved_inputs': ['DiamondIntegral.Section7.Lemma714Reduce.lemma714 : FiberwiseInput.Lemma714 M G (Lemma 7.14, isp:VF:fiberwise:contract), formerly a temporary input (author decision of 2026-11-19), proved in the Lemma714* modules.', 'DiamondIntegral.Section7.Lemma720.lemma720 : TwoCellInput.Lemma720 M G (Lemma 7.20, decom:into:2:units), formerly a temporary input (author decision of 2026-11-19), proved in the Lemma720* modules.'],
    'unfinished': ['Lemma 7.10 multiplicative part (products).', 'Object-level converse of BlowupResults: a class-level length-one blowup is realised by literal disjoint subobjects (Definition 7.2 wording).', 'Object-level form of Lemma 7.12 (an isomorphism mu L U^flat = mu L U in mu VF^diamond rather than equality in K_+); later uses need only the class form.', 'Lemma 7.11 in the approved partial-lift form (Lemma 7.13 with head start is built in Lemma714Compare).', 'Corollary 7.27 as equalities of ring maps (needs the integral as a ring map, which rests on the false intermediate-forms input).']
}
(RECORD/'status.json').write_text(json.dumps(status,indent=2)+'\n')
print(f'PASS: {len(declarations)} full declaration types and axiom records; Section 7 results 7.3-7.10 (7.10 additive), 7.11 (full lift, classes), 7.12 (classes), 7.13 (head start 0), 7.14, 7.15, 7.16-7.19, 7.20, 7.21 (uniform), 7.22, 7.23, 7.24 and 7.26 in degree 0, 7.24-7.26 in positive degree on the intermediate-forms input (false as stated, GAP-REPAIRS 16), 7.27 on classes, 7.28 audited.')
