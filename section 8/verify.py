#!/usr/bin/env python3
"""Build Section 8 and audit complete public types and logical axioms."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
sys.path.insert(0, str(ROOT / 'verification'))
from proof_sources import read_source
RECORD = SECTION / 'verification'
RECORD.mkdir(exist_ok=True)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
sources = sorted(SECTION.glob('*.lean'))
declarations = []
for source in sources:
    body = read_source(source)
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
        declaration = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|inductive)\s+([\w.']+)", command)
        if declaration:
            namespace = '.'.join(name for kind, name in frames if kind == 'namespace')
            if not namespace.startswith('DiamondIntegral.Section8'):
                raise SystemExit(f'FAIL: declaration outside DiamondIntegral.Section8 in {source.name}: {namespace}')
            declarations.append(namespace + '.' + declaration.group(1))
if len(declarations) != len(set(declarations)):
    raise SystemExit('FAIL: duplicate declaration in audit manifest')

subprocess.run(['lake', 'build', 'section 8'], cwd=ROOT, check=True,
    stdout=(RECORD/'build.log').open('w'), stderr=subprocess.STDOUT)
audit = RECORD/'Audit.lean'
audit.write_text(''.join(f'import «section 8».{p.stem}\n' for p in sources) + '\n' + '\n'.join(
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
    'scope': 'Section 8 (Motivic Milnor fiber), every numbered result of the revised manuscript except Remark 8.12 (commentary) and the example of Remark 8.13, with no input beyond the ACVF model and the Puiseux ambient of Section 5, except the etale chart hypotheses for smooth X listed under accepted_inputs. Lemma 8.2 as the definition of h_m (Hm.hm, hm_objectClass; localization Rloc and etaHm). Lemma 8.3 (Hm.lemma_8_3: eta h_m kills the natural part of J_var; hm_generator). Lemma 8.5 in set form (Truncation.lemma_8_5_sets) and for classes (fullClass, fullClass_cutoff, fullClass_scale; truncations are diagonal constructible, truncObject, definable_agree). Lemma 8.6 (chain_teq: special covariant chains preserve normalized truncation classes, with anisotropic cutoffs for centripetal steps; lift_class; integral_lift). Lemma 8.9 (PuiseuxValues.lemma_8_9, lemma_8_9_rat; Hrushovski-Loeser Lemma 8.5.2 proved directly, Prism.hasLimit_latticeSeries). Theorem 8.11 (theorem_8_11_rv_ring, theorem_8_11_quotient, theorem_8_11_vf; Milnor.theorem_8_11_milnor for X = A^d; theorem_8_11_smooth). (z:coeff:change) (Lemma86.milnor_zeta_coeff, z_coeff_change for X = A^d; zeta_coeff_of_form_one; MilnorSmoothJets.z_coeff_change_smooth for smooth affine X). Remark 8.14 (VolComparison.remark_8_14, milnor_fiber_vol, milnor_fiber_vol_smooth). Remark 8.15 (Remark815.remark_8_15_integral, remark_8_15, remark_8_15_affine, remark_8_15_smooth, remark_8_15_milnor, remark_8_15_milnor_smooth; SameType.same_type by quantifier elimination). Remark 8.7 (Remark87.remark_8_7: the object X = {0 < vrv < 1} with f(u) = u^2 is not isomorphic, by a weight-preserving bijection with definable inverse, to any set covered by a part with finitely many weights and products W x Delta-sharp with W finite; germ, finite_level). Statements with every hypothesis supplied (Closed.theorem_7_26, theorem_7_26_graded, theorem_8_11, remark_8_14, remark_8_15): the Puiseux ambient chosen from puiseuxAmbient_nonempty, a valuation compatible with the language, and the base element t of nontrivial value. Section 8.1.1, the old Lemma 8.7 and the general claims of Remark 8.13 were deleted from the manuscript by the author in the final review.',
    'lean': subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip(),
    'repository_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'packages': {p['name']:p['rev'] for p in manifest['packages']},
    'declarations': declarations,
    'allowed_axioms': sorted(ALLOWED),
    'sources': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'verification_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'temporary_inputs': [],
    'accepted_inputs': ['DiamondIntegral.Section8.Milnor.EtaleChart: etale chart of a smooth affine X at the origin (Hensel\'s lemma), an explicit hypothesis of the smooth-X results only (author instruction of 2026-11-21); proved for X = A^d (etaleChart_affine).', 'DiamondIntegral.Section8.Truncation.EtaleCoords: etale coordinates with a 1-Lipschitz inverse (Hensel\'s lemma), an explicit hypothesis of z_coeff_change_smooth only; it implies EtaleChart and is proved for X = A^d (etaleCoords_affine). See section 8/CITED-INPUTS.md.'],
    'unfinished': []
}
(RECORD/'status.json').write_text(json.dumps(status,indent=2)+'\n')
print(f'PASS: {len(declarations)} full declaration types and axiom records; Section 8 results 8.2-8.3, 8.5-8.7, 8.9, 8.11, (z:coeff:change), 8.14 and 8.15, and the statements with every hypothesis supplied, audited.')
