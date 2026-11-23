#!/usr/bin/env python3
"""Locate Lean declarations in this repository and in its pinned providers.

Most modules of this repository are compatibility imports whose proofs live in a
pinned provider package (hilbert-mathlib, Fubini-theorems and the upstream
paper packages; see SHARED-FOUNDATION.json and EXTRACTED-FOUNDATIONS.json).
The index below reads the Lean sources of the repository and of each provider
checkout, tracks `namespace`, `section` and `end`, skips comments, and records
for every fully qualified declaration name the file and the 1-based line of its
keyword. The blueprint uses it to anchor its source links.

Provider checkouts are read from `.lake/packages/<name>` (as Lake places them),
or from the directory in the environment variable BLUEPRINT_PACKAGES.
"""
from pathlib import Path
from urllib.parse import quote
import json
import os
import re

ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = 'https://github.com/daviddhilbert/diamond-integral'
PROVIDERS = ['hilbert-mathlib', 'fubini_theorems', 'integration_in_acvf',
             'special_transformations', 'acvf_qe']

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*'
    r'(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+'
    r'(?!:)([^\s:({\[]+)')
NAMESPACE = re.compile(r'^namespace\s+(\S+)')
SECTION = re.compile(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')


def strip_comments(lines):
    """Yield (line_number, text) with block and line comments removed."""
    depth = 0
    for number, line in enumerate(lines, 1):
        out = []
        i = 0
        while i < len(line):
            if line.startswith('/-', i):
                depth += 1
                i += 2
            elif depth and line.startswith('-/', i):
                depth -= 1
                i += 2
            elif not depth and line.startswith('--', i):
                break
            else:
                if not depth:
                    out.append(line[i])
                i += 1
        yield number, ''.join(out)


def declarations(path):
    """Return {full_name: line} for one Lean source file."""
    stack = []
    found = {}
    lines = path.read_text(encoding='utf-8-sig').splitlines()
    for number, text in strip_comments(lines):
        text = text.strip()
        if not text:
            continue
        m = NAMESPACE.match(text)
        if m:
            stack.append(('ns', m[1].split('.')))
            continue
        m = SECTION.match(text)
        if m:
            stack.append(('sec', m[1]))
            continue
        m = END.match(text)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL.match(text)
        if m and m[1] != 'instance':
            name = m[2]
            if name.startswith('_root_.'):
                full = name[len('_root_.'):]
            else:
                prefix = [c for kind, value in stack if kind == 'ns' for c in value]
                full = '.'.join(prefix + [name])
            found.setdefault(full, number)
    return found


def manifest():
    """{provider: (repository URL, revision)} from lake-manifest.json."""
    data = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    pins = {}
    for package in data['packages']:
        name = package['name'].strip('«»')
        if name in PROVIDERS:
            pins[name] = (package['url'].removesuffix('.git'), package['rev'])
    return pins


def packages_dir():
    return Path(os.environ.get('BLUEPRINT_PACKAGES', ROOT / '.lake/packages'))


def own_files():
    files = [p for p in ROOT.glob('section */**/*.lean') if '.lake' not in p.parts and '.scratch' not in p.parts]
    files.append(ROOT / 'DiamondIntegral.lean')
    return sorted(files)


def provider_files(name):
    base = packages_dir() / name
    return sorted(p for p in base.rglob('*.lean') if '.lake' not in p.relative_to(base).parts)


def index():
    """{full_name: [(provider or None, relative file, line), ...]}."""
    found = {}
    for path in own_files():
        for name, line in declarations(path).items():
            found.setdefault(name, []).append((None, path.relative_to(ROOT).as_posix(), line))
    for provider in PROVIDERS:
        base = packages_dir() / provider
        if not base.is_dir():
            raise SystemExit(f'Missing provider checkout {base}; see blueprint/README.md')
        for path in provider_files(provider):
            for name, line in declarations(path).items():
                found.setdefault(name, []).append((provider, path.relative_to(base).as_posix(), line))
    return found


def resolve(locations):
    """The defining location: this repository first, then the first provider in PROVIDERS order."""
    order = {None: -1, **{p: i for i, p in enumerate(PROVIDERS)}}
    return min(locations, key=lambda loc: order[loc[0]])


def source_root(provider):
    return ROOT if provider is None else packages_dir() / provider


def line_matches(provider, file, line, name):
    text = (source_root(provider) / file).read_text(encoding='utf-8-sig').splitlines()[line - 1]
    short = re.escape(name.split('.')[-1])
    return re.search(r'\b(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom)\s+(?:\S*\.)?'
                     + short + r'(?![\w.])', text) is not None


def url(provider, file, line, revision, pins):
    base, rev = (REPOSITORY, revision) if provider is None else pins[provider]
    return f'{base}/blob/{rev}/{quote(file)}#L{line}'
