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
        declaration = re.match(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|structure|inductive)\s+([\w.]+)', command)
        if declaration:
            namespace = '.'.join(name for kind, name in frames if kind == 'namespace')
            if not namespace.startswith('DiamondIntegral.Section7'):
                raise SystemExit(f'FAIL: declaration outside Section 7 in {source.name}')
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
    'scope': 'Section 7 formalization in progress. Checked so far: the data of Definition 7.2 (defn:blowup:coa) with bounded variable apertures (actual original-base definable aperture graph, nonzero, 0 <= vrv <= one named bound), the inactive structural projection, the shell and separately tagged endpoint, the blown-up structural map s*f_j, and the finite-fibre property on both pieces from the finite-to-one condition, with the Remark 7.4 coordinate bounds. No numbered Section 7 result beyond these components is claimed.',
    'lean': subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip(),
    'repository_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'packages': {p['name']:p['rev'] for p in manifest['packages']},
    'declarations': declarations,
    'allowed_axioms': sorted(ALLOWED),
    'sources': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'verification_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'unfinished': ['Package the blowup as a bounded chart and identify it with the relative annular object of Notation 4.17.', 'Lemmas 7.5-7.23, Proposition 7.24, Remark 7.25 and Theorem 7.26 with J_var remain to be formalized.']
}
(RECORD/'status.json').write_text(json.dumps(status,indent=2)+'\n')
print(f'PASS: {len(declarations)} full declaration types and axiom records; Section 7 components audited; numbered results pending.')
