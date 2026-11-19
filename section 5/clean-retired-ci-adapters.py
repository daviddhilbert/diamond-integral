#!/usr/bin/env python3
"""Restore only the two recognized retired adapters in an Actions cache.

Fresh checkouts require no changes. Unknown edits are preserved and rejected.
Local dependency verification remains read-only.
"""
import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / '.lake/packages/integration_in_acvf'


def main():
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise SystemExit('This one-time cache migration runs only in GitHub Actions.')
    record = json.loads((ROOT / 'section 5/reference/integration-section6-scope-adapter.json').read_text())
    expected = json.loads((ROOT / 'lake-manifest.json').read_text())
    pin = next(p['rev'] for p in expected['packages'] if p['name'] == 'integration_in_acvf')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PACKAGE, text=True).strip()
    if head != pin:
        raise SystemExit('Refusing cache migration at an unexpected dependency revision.')
    pending = []
    for name, old_hash in record['historical_adapter_files'].items():
        path = PACKAGE / name
        upstream = subprocess.check_output(['git', 'show', 'HEAD:' + name], cwd=PACKAGE)
        current = path.read_bytes()
        if current == upstream:
            continue
        if hashlib.sha256(current).hexdigest() != old_hash:
            raise SystemExit('Unrecognized cached source edit; preserving it: ' + name)
        pending.append((path, upstream))
    for path, source in pending:
        path.write_bytes(source)
    print(f'Restored {len(pending)} recognized retired adapters to published source.')


if __name__ == '__main__':
    main()
