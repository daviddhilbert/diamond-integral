"""Follow checked compatibility imports when auditing public source declarations."""
from pathlib import Path
import hashlib
import json
from relocated_sources import read_relocated


def read_source(path):
    path = Path(path)
    root = Path(__file__).resolve().parents[1]
    relocated = read_relocated(root, path)
    if relocated is not None:
        return relocated
    relative = str(path.relative_to(root))
    manifest = root / 'SHARED-FOUNDATION.json'
    if manifest.exists():
        record = json.loads(manifest.read_text())
        for item in record['modules']:
            if item['path'] == relative:
                provider = root / '.lake/packages/hilbert-mathlib' / item['target_path']
                if hashlib.sha256(provider.read_bytes()).hexdigest() != item['extracted_sha256']:
                    raise RuntimeError('Relocated proof source changed: ' + str(provider))
                if hashlib.sha256(path.read_bytes()).hexdigest() != item['compatibility_sha256']:
                    raise RuntimeError('Compatibility import changed: ' + str(path))
                return provider.read_text()
    return path.read_text()
