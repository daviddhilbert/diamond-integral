#!/usr/bin/env python3
"""Check published dependency sources and retain the scoped Section 6 adapters.

Run after Lake has fetched the pinned packages. Only a pinned upstream file
or the already prepared file is accepted; unrelated local edits are preserved.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
OVERLAY = SECTION / "dependency-overlay"
PACKAGE = ROOT / ".lake/packages/integration_in_acvf"


def digest(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def compatibility(check: bool) -> None:
    layers = [
        ("special_transformations", "section 2/reuse/manifest.json", "section 2/prepare-reuse.py"),
        ("integration_in_acvf", "section 3/reuse/integration-manifest.json",
         "section 3/prepare-integration-reuse.py"),
    ]
    for index, (package, record, script) in enumerate(layers):
        manifest = json.loads((ROOT / record).read_text())
        directory = ROOT / ".lake/packages" / package
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory,
                                           text=True).strip()
        if revision != manifest["base_revision"]:
            raise SystemExit(f"Unexpected {package} revision: {revision}")
        if not check:
            spec = importlib.util.spec_from_file_location(f"section5_compatibility_{index}", ROOT / script)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            module.prepare()
        for name, identity in manifest["files"].items():
            if digest(directory / name) != identity["after"]:
                raise SystemExit(f"Compatibility source mismatch: {package}/{name}")


def prepare(check: bool = False) -> int:
    manifest = json.loads((OVERLAY / "manifest.json").read_text())
    if not (PACKAGE / ".git").exists():
        raise SystemExit("Pinned dependencies are missing; run lake update first.")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=PACKAGE,
                                       text=True).strip()
    if revision != manifest["base_revision"]:
        raise SystemExit(f"Unexpected integration_in_acvf revision: {revision}")
    pending = []
    for name, identity in manifest["files"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise SystemExit(f"Invalid overlay path: {name}")
        source = OVERLAY / "integration_in_acvf" / relative
        target = PACKAGE / relative
        if digest(source) != identity["after"]:
            raise SystemExit(f"Overlay checksum mismatch: {name}")
        current = digest(target)
        if current == identity["after"]:
            continue
        if check or current != identity["before"]:
            raise SystemExit(f"Dependency source differs from the recorded state; preserving it: {name}")
        pending.append((source, target))
    compatibility(check)
    for source, target in pending:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source.read_bytes())
    return len(manifest["files"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check prepared sources without writing them.")
    arguments = parser.parse_args()
    count = prepare(arguments.check)
    print(f"Verified {count} recorded Section 5/6 sources and 39 published compatibility sources")
