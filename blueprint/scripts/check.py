#!/usr/bin/env python3
"""Check, or regenerate, the blueprint of diamond-integral.

`blueprint/nodes.json` is the registry: one node per numbered item of the paper
`paper/bounded-integral-motivic-milnor-fiber.tex` that the blueprint covers,
with its statement, proof outline, dependencies, formalization status and Lean
declarations, and `blueprint/sections.json` holds the section introductions.
From these the script generates `src/content.tex` and `src/source-links.tsv`.

Checks (default):
  * every node's dependencies are nodes and the dependency graph is acyclic;
  * every declaration is located by `lean_anchors.py` at the recorded provider,
    file and line, and the line declares it;
  * every declaration is in an audited list: a section receipt of this
    repository or, for results recalled from the Fubini paper, the public
    contract of the pinned Fubini-theorems package;
  * `src/content.tex` and `src/source-links.tsv` equal what the registry generates;
  * the fingerprinted inputs are unchanged and the Lean sources equal those of
    the linked revision.
With --rendered, the rendered site under `blueprint/web` is also checked: every
source link appears, and every node of the SVG graph links to a statement.
With --write, anchors, the generated files and the fingerprints are refreshed
(names, statements and dependencies are never changed); --revision REV also
moves the linked revision, which must be a pushed commit with the same sources.
"""
from pathlib import Path
import argparse
import hashlib
import html
import json
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from urllib.parse import unquote, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_anchors  # noqa: E402

ROOT = lean_anchors.ROOT
BP = ROOT / 'blueprint'
NODES = BP / 'nodes.json'
SECTIONS = BP / 'sections.json'
CONTENT = BP / 'src/content.tex'
LINKS = BP / 'src/source-links.tsv'
RECEIPT = BP / 'proof-source-manifest.json'
PAPER = 'paper/bounded-integral-motivic-milnor-fiber.tex'
FINGERPRINTED = [PAPER, 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain',
                 'SHARED-FOUNDATION.json', 'EXTRACTED-FOUNDATIONS.json',
                 'section 2/verification/status.json', 'section 3/verification/VERIFICATION.json',
                 'section 4/verification/status.json', 'section 6/verification/status.json',
                 'section 7/verification/status.json', 'section 8/verification/status.json']
KINDS = {'definition', 'lemma', 'proposition', 'theorem', 'corollary', 'remark', 'imported', 'assumption',
         'formula'}
STATUSES = {'formalized', 'partial', 'not formalized'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding='utf-8'))


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def audited_names():
    """Names whose types and axioms a receipt of this repository records."""
    names = set()
    s2 = load(ROOT / 'section 2/verification/status.json')
    names |= set(s2['axioms']) | set(s2['public_theorems']) | set(s2['reuse_theorems'])
    s3 = load(ROOT / 'section 3/verification/VERIFICATION.json')
    for key in ('public_theorems', 'definitions_printed', 'typeclass_instances', 'groupoid_instances'):
        names |= set(s3[key])
    names |= set(load(ROOT / 'section 4/verification/status.json')['declarations'])
    for n in (6, 7, 8):
        names |= set(load(ROOT / f'section {n}/verification/status.json')['declarations'])
    # the printed types of the Section 2 and 3 headline audits also cover their definitions
    printed = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?'
                         r'(?:def|theorem|opaque|structure|inductive|class|abbrev)\s+([^\s:]+?)(?:\.\{[^}]*\})?\s*:')
    for n in (2, 3):
        for line in (ROOT / f'section {n}/verification/headline-audit.txt').read_text(encoding='utf-8').splitlines():
            m = printed.match(line)
            if m:
                names.add(m[1])
    return names


def fubini_contract():
    path = lean_anchors.packages_dir() / 'fubini_theorems/verification/public-contract.json'
    return {d['name'] for d in load(path)['declarations']}


def item_number(node):
    m = re.search(r'(\d+)\.(\d+)$', node['number'])
    return (int(m[1]), int(m[2])) if m else None


def environment(node):
    kind, lines = node['kind'], []
    if kind != 'assumption':
        counter = 'formula' if kind == 'formula' else 'theorem'
        lines.append(f'\\setcounter{{{counter}}}{{{item_number(node)[1] - 1}}}')
    title = node['title']
    if '[' in title or ']' in title:
        title = '{' + title + '}'  # brackets inside an optional argument
    lines.append(f'\\begin{{{kind}}}[{title}]')
    lines.append(f'\\label{{{node["id"]}}}')
    names = [d['name'] for d in node['declarations']]
    if names:
        lines.append('\\lean{' + ', '.join(names) + '}')
    if node['lean_status'] != 'not formalized':
        lines.append('\\leanok')
    if node['uses']:
        lines.append('\\uses{' + ', '.join(node['uses']) + '}')
    lines.append(node['statement'])
    if node.get('scope_note'):
        lines.append('')
        lines.append('\\emph{Formalization.} ' + node['scope_note'])
    lines.append(f'\\end{{{kind}}}')
    if node.get('proof'):
        lines.append('')
        lines.append('\\begin{proof}')
        if node['proof_uses']:
            lines.append('\\uses{' + ', '.join(node['proof_uses']) + '}')
        if node['lean_status'] == 'formalized':
            lines.append('\\leanok')
        lines.append(node['proof'])
        lines.append('\\end{proof}')
    return '\n'.join(lines)


def generate_content(nodes, sections):
    parts = ['% Generated by blueprint/scripts/check.py --write from nodes.json and sections.json.',
             '% Edit those files, not this one.']
    for section in sections:
        parts.append('')
        parts.append(f'\\section{{{section["title"]}}}')
        if section.get('label'):
            parts.append(f'\\label{{{section["label"]}}}')
        parts.append(section['intro'])
        for node in nodes:
            if node['section'] == section['number']:
                parts.append('')
                parts.append(environment(node))
    return '\n'.join(parts) + '\n'


def check_registry(nodes, sections, errors):
    ids = [n['id'] for n in nodes]
    if len(set(ids)) != len(ids):
        errors.append('duplicate node ids')
    known = set(ids)
    section_numbers = {s['number'] for s in sections}
    by_id = {n['id']: n for n in nodes}
    for n in nodes:
        where = f'node {n["id"]}'
        if not re.fullmatch(r'[A-Za-z0-9-]+', n['id']):
            errors.append(f'{where}: id must use letters, digits and hyphens')
        if n['kind'] not in KINDS:
            errors.append(f'{where}: unknown kind {n["kind"]}')
        if n['lean_status'] not in STATUSES:
            errors.append(f'{where}: unknown status {n["lean_status"]}')
        if n['section'] not in section_numbers:
            errors.append(f'{where}: unknown section {n["section"]}')
        if n['kind'] != 'assumption':
            number = item_number(n)
            if not number or number[0] != n['section']:
                errors.append(f'{where}: number {n["number"]} does not match section {n["section"]}')
        if (n['lean_status'] == 'not formalized') != (not n['declarations']):
            errors.append(f'{where}: declarations must be empty exactly when not formalized')
        if n['lean_status'] != 'formalized' and not n.get('scope_note'):
            errors.append(f'{where}: a {n["lean_status"]} node needs a scope note')
        for dep in n['uses'] + n['proof_uses']:
            if dep not in known:
                errors.append(f'{where}: unknown dependency {dep}')
        for field in ('statement', 'proof', 'scope_note', 'title'):
            text = n.get(field) or ''
            if text.count('{') != text.count('}'):
                errors.append(f'{where}: unbalanced braces in {field}')
            if re.search(r'\\(ref|eqref|cite|label|begin\{(?!itemize|enumerate))', text) or '%' in text.replace('\\%', ''):
                errors.append(f'{where}: {field} uses \\ref, \\cite, \\label, an environment or a comment')
    for section in sections:
        for target in re.findall(r'\\ref\{([^}]+)\}', section['intro']):
            if target not in known:
                errors.append(f'section {section["number"]}: reference to unknown node {target}')
    visiting, visited = set(), set()

    def visit(node_id):
        if node_id in visiting:
            errors.append(f'cyclic dependencies through {node_id}')
            return
        if node_id in visited or node_id not in by_id:
            return
        visiting.add(node_id)
        for dep in by_id[node_id]['uses'] + by_id[node_id]['proof_uses']:
            visit(dep)
        visiting.discard(node_id)
        visited.add(node_id)

    for node_id in ids:
        visit(node_id)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--write', action='store_true', help='refresh anchors, generated files and fingerprints')
    parser.add_argument('--revision', help='with --write: the commit the source links point to')
    parser.add_argument('--rendered', action='store_true', help='also check the rendered site in blueprint/web')
    args = parser.parse_args()
    errors = []
    nodes, sections = load(NODES), load(SECTIONS)
    receipt = load(RECEIPT)
    check_registry(nodes, sections, errors)

    index = lean_anchors.index()
    pins = lean_anchors.manifest()
    audited, fubini = audited_names(), fubini_contract()
    if args.write and args.revision:
        receipt['proof_revision'] = args.revision
    revision = receipt['proof_revision']
    registry = {}
    for n in nodes:
        for d in n['declarations']:
            name, where = d['name'], f'node {n["id"]}'
            if name not in index:
                errors.append(f'{where}: no declaration {name} in this repository or its providers')
                continue
            provider, file, line = lean_anchors.resolve(index[name])
            if args.write:
                d['provider'], d['file'], d['line'] = provider, file, line
            if (d.get('provider'), d['file'], d['line']) != (provider, file, line):
                errors.append(f'{where}: {name} is declared at {provider or "this repository"}:{file}:{line}')
            elif not lean_anchors.line_matches(provider, file, line, name):
                errors.append(f'{where}: line {file}:{line} does not declare {name}')
            if n['kind'] == 'imported':
                if name not in fubini:
                    errors.append(f'{where}: {name} is not in the Fubini public contract')
            elif name not in audited:
                errors.append(f'{where}: {name} is in no section receipt')
            registry[name] = lean_anchors.url(provider, file, line, revision, pins)

    content = generate_content(nodes, sections)
    links = ''.join(f'{name}\t{target}\n' for name, target in registry.items())
    if args.write:
        dump(NODES, nodes)
        CONTENT.write_text(content, encoding='utf-8')
        LINKS.write_text(links, encoding='utf-8')
        receipt['pins'] = {name: rev for name, (_, rev) in sorted(pins.items())}
        receipt['sha256'] = {name: digest(ROOT / name) for name in FINGERPRINTED}
        dump(RECEIPT, receipt)
    if CONTENT.read_text(encoding='utf-8') != content:
        errors.append('src/content.tex differs from the registry; run with --write')
    if LINKS.read_text(encoding='utf-8') != links:
        errors.append('src/source-links.tsv differs from the registry; run with --write')
    if set(receipt['sha256']) != set(FINGERPRINTED):
        errors.append('proof-source-manifest.json does not list exactly the fingerprinted inputs')
    for name, expected in receipt['sha256'].items():
        if (ROOT / name).is_file() and digest(ROOT / name) != expected:
            errors.append(f'input changed since the blueprint was checked: {name}')
    if receipt.get('pins') != {name: rev for name, (_, rev) in sorted(pins.items())}:
        errors.append('provider pins differ from lake-manifest.json')

    available = subprocess.run(['git', 'cat-file', '-e', revision + '^{commit}'], cwd=ROOT,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    if available:
        same = subprocess.run(['git', 'diff', '--quiet', revision, '--', ':(glob)section */**/*.lean',
                               'DiamondIntegral.lean', 'lakefile.toml', 'lake-manifest.json'], cwd=ROOT).returncode == 0
        if not same:
            errors.append(f'Lean sources differ from the linked revision {revision}')
    else:
        errors.append(f'linked revision {revision} is not available in this checkout')

    if args.rendered:
        web = BP / 'web'
        pages = list(web.glob('*.html'))
        if not (web / 'index.html').is_file() or not pages:
            errors.append('missing rendered site')
        else:
            text = html.unescape('\n'.join(p.read_text(encoding='utf-8') for p in pages))
            for name, target in registry.items():
                if target not in text:
                    errors.append(f'missing rendered Lean link: {name}')
            svg = ET.parse(web / 'dependency-graph.svg').getroot()
            graph_nodes = [e for e in svg.iter() if e.tag.endswith('}g') and e.attrib.get('class') == 'node']
            if len(graph_nodes) != len(nodes):
                errors.append(f'expected {len(nodes)} graph nodes, found {len(graph_nodes)}')
            for g in graph_nodes:
                anchors = [a for a in g.iter() if a.tag.endswith('}a')]
                if not anchors:
                    errors.append('unlinked graph node')
                for a in anchors:
                    href = a.attrib.get('{http://www.w3.org/1999/xlink}href', a.attrib.get('href', ''))
                    u = urlsplit(href)
                    target = web / unquote(u.path)
                    if u.scheme or not target.is_file():
                        errors.append(f'graph link without a local target: {href}')
                    elif u.fragment and not re.search(r'(?:id|name)=["\']' + re.escape(unquote(u.fragment)) + r'["\']',
                                                      target.read_text(encoding='utf-8')):
                        errors.append(f'graph link to a missing statement: {href}')

    if errors:
        print('\n'.join(errors), file=sys.stderr)
        sys.exit(1)
    counts = {s: sum(n['lean_status'] == s and n['kind'] != 'assumption' for n in nodes) for s in sorted(STATUSES)}
    print(json.dumps({'status': 'PASS', 'nodes': len(nodes),
                      'hypotheses': sum(n['kind'] == 'assumption' for n in nodes), 'by_status': counts,
                      'declarations': len(registry), 'linked_revision': revision,
                      'rendered': args.rendered}))


if __name__ == '__main__':
    main()
