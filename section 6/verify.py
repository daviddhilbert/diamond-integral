#!/usr/bin/env python3
"""Build Section 6 and audit complete public types and logical axioms."""
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
        declaration = re.match(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|inductive)\s+([\w.]+)', command)
        if declaration:
            namespace = '.'.join(name for kind, name in frames if kind == 'namespace')
            if not namespace.startswith('DiamondIntegral.Section6'):
                raise SystemExit(f'FAIL: declaration outside Section 6 in {source.name}')
            declarations.append(namespace + '.' + declaration.group(1))
if len(declarations) != len(set(declarations)):
    raise SystemExit('FAIL: duplicate declaration in audit manifest')

subprocess.run(['lake', 'build', '«section 6».Section'], cwd=ROOT, check=True,
    stdout=(RECORD/'build.log').open('w'), stderr=subprocess.STDOUT)
audit = RECORD/'Audit.lean'
audit.write_text('import «section 6».Section\n\n' + '\n'.join(
    f'#check @{name}\n#print {name}\n#print axioms {name}' for name in declarations) + '\n')
checked = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=ROOT,
    check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout
(RECORD/'types-and-axioms.txt').write_text(checked)
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", checked)
axioms += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", checked)]
if len(axioms) != len(declarations):
    raise SystemExit(f'FAIL: expected {len(declarations)} axiom records, got {len(axioms)}')
for name, names in axioms:
    actual = {n.strip() for n in names.split(',') if n.strip()}
    if actual - ALLOWED:
        raise SystemExit(f'FAIL: {name} uses {actual - ALLOWED}')
manifest = json.loads((ROOT/'lake-manifest.json').read_text())
status = {
    'status': 'PASS',
    'scope': 'The manuscript now applies the bounded variable aperture and actual continuous VF endpoint data in Definition 6.11, with the corresponding first-zero proof and literal conjugacy in Lemma 6.38. RelativeApertureData and RelativeApertureChain implement this class in arbitrary VF arity; the original CentripetalData and SpecialCovariantChain remain its constant-aperture subclass and retain their existence witnesses. The new primitive has actual definable graphs, bounds, exact source membership and full core images, proper covariant homeomorphisms and the approved almost-everywhere unit total Jacobian. Both scalar operations and the unary constructions embed with identical point maps. The complete lemma_6_38_bounded_variable_apertures begins with original proper objects, actual Gamma forms with open fixed-label levels and the generic measure identity over the VF-generated base. It constructs actual bounded aperture graphs, separated paired whole cores, finite first-zero executions, both precise variable chains, the literal conjugate, actual RV bijection and the volume identity at every label, allowing arbitrary retained RV fibres. Earlier complete numbered results remain: 6.5–6.9, approved AE 6.14 and relation preparation 6.16; simultaneous proper preparation 6.19 and measured preparation 6.21 in every VF arity and arbitrary RV dimension, including zero arity; Gamma bounds 6.22–6.23; standard contractions 6.27 for arbitrary proper sources in every positive dimension and coordinate order with the permitted normalization, full original-source lifts, measured forms, protected families and head starts; all four 6.29 factorization variants in every positive degree; literal unary finitary lifting 6.30; measured and unmeasured everywhere-Jacobian lifting 6.31 in every degree; and measured relatively unary VF chain lifting 6.33 in every positive degree. Exact double bounds and original retained labels are kept. Existing scalar existence proofs remain admissible by inclusion; no new existence statement is inferred solely from enlarging the class. Pure RV aperture compatibility now belongs to Section4 and is imported through thin compatibility modules: ordinary ray cancellation, arbitrary bounded aperture graphs, annihilation by the constructed bounded retraction, degree-zero preservation and the full measured comparison into (P). The completed approved Section5 sources and their audited dependency overlay are integrated as the upstream baseline, without modifying the Section5 session worktree. Section1 quotient descriptions and the new Section4 relative ideal and compatibility lemma are manuscript consequences of the aperture change. Sections2, 3 and 5 need no aperture-dependent text edits. Section7 and Section8 main text is preserved and their required synchronized changes are handoff notes, not certified kernel or specialization theorems. All declarations are checked at their full types and transitive logical axiom dependencies, with exact package pins and source hashes.',
    'lean': subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip(),
    'repository_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'packages': {p['name']:p['rev'] for p in manifest['packages']},
    'declarations': declarations,
    'allowed_axioms': sorted(ALLOWED),
    'sources': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'verification_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'unfinished': ["Section7 must synchronize Definition7.2 with the applied bounded variable Definition6.11, instantiate actual variable blowup words and continuous VF generator lifts, assemble head starts, full witness descent and contraction-order comparisons, and prove the revised 7.26 kernel for the explicitly defined relative ideal. These are deferred to its own session at the author's request; no complete native 7.26 theorem is claimed.", 'Section8 must check the equivariant endpoint-graph trace and specialization against the new relative ideal. Algebraic factor identities and RV-affinity/full-row descent support are available, but they do not certify complete downstream preservation. The old scalar Section4 ideal and its pure RV presentation remain distinct and unchanged.']
}
(RECORD/'status.json').write_text(json.dumps(status,indent=2)+'\n')
print(f'PASS: {len(declarations)} full declaration types and axiom records; applied Section 6 aperture revision audited; downstream assembly deferred.')
