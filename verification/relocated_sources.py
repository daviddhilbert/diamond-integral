"""Resolve and verify extracted proof sources behind compatibility imports."""
from pathlib import Path
from functools import lru_cache
import hashlib
import json
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


@lru_cache(maxsize=8)
def _load(path, modified, size):
    record = json.loads(path.read_text())
    record['_by_path'] = {item['path']: item for item in record['modules']}
    return record


def load(root):
    path = Path(root) / 'EXTRACTED-FOUNDATIONS.json'
    if not path.exists():
        return None
    stat = path.stat()
    return _load(path, stat.st_mtime_ns, stat.st_size)


def provider_path(root, item):
    return Path(root) / '.lake/packages' / item['package'] / item['target_path']


def read_relocated(root, path):
    record = load(root)
    if record is None:
        return None
    relative = str(Path(path).relative_to(root))
    item = record['_by_path'].get(relative)
    if item is None:
        return None
    if digest(path) != item['compatibility_sha256']:
        raise RuntimeError('Changed extracted compatibility import: ' + relative)
    sources = [item] + item.get('additional_sources', [])
    result = []
    for source in sources:
        target = provider_path(root, source)
        if digest(target) != source['extracted_sha256']:
            raise RuntimeError('Changed extracted proof source: ' + str(target))
        result.append(target.read_text())
    return '\n'.join(result)


def verify(root):
    root = Path(root)
    record = load(root)
    if record is None:
        return None
    pins = json.loads((root / 'lake-manifest.json').read_text())
    by_name = {p['name'].strip('«»'): p for p in pins['packages']}
    providers = {}
    for name, revision in record['providers'].items():
        package = root / pins['packagesDir'] / name
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=package, text=True).strip()
        if actual != revision or by_name[name]['rev'] != revision:
            raise RuntimeError('Extracted provider differs from its exact pin: ' + name)
        changed = subprocess.check_output(['git', 'diff', 'HEAD', '--name-only', '--', '*.lean'],
                                          cwd=package, text=True)
        if changed:
            raise RuntimeError('Extracted provider has changed Lean sources: ' + name)
        providers[name] = revision
    evidence = {}
    for item in record['modules']:
        read_relocated(root, root / item['path'])
        evidence[item['module']] = {
            'provider': item['target_module'],
            'provider_source_sha256': item['extracted_sha256'],
            'compatibility_sha256': item['compatibility_sha256'],
            'additional_sources': item.get('additional_sources', []),
        }
    receipt = {'status': 'PASS', 'providers': providers, 'modules': evidence}
    output = root / '.scratch/extracted-foundations.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print('Extracted foundations:', len(evidence), 'checked compatibility imports and exact provider pins.')
    return receipt
