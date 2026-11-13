#!/usr/bin/env python3
"""Prepare the Integration in ACVF consumer proof compatibility patch."""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
PACKAGE = ROOT / ".lake/packages/integration_in_acvf"


def prepare() -> dict:
    manifest = json.loads((SECTION / "reuse/integration-manifest.json").read_text())
    patch = SECTION / "reuse/integration-open-radius.patch"
    if hashlib.sha256(patch.read_bytes()).hexdigest() != manifest["patch_sha256"]:
        raise SystemExit("FAIL: integration compatibility patch checksum mismatch")
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=PACKAGE, text=True
    ).strip()
    if revision != manifest["base_revision"]:
        raise SystemExit(f"FAIL: unexpected integration compatibility revision: {revision}")
    current = subprocess.check_output(
        ["git", "diff", "--no-ext-diff", "--binary", "--", "*.lean"], cwd=PACKAGE
    )
    if current != patch.read_bytes():
        if current:
            raise SystemExit("FAIL: integration dependency has other Lean edits; leaving them untouched")
        subprocess.run(["git", "apply", "--check", str(patch)], cwd=PACKAGE, check=True)
        subprocess.run(["git", "apply", str(patch)], cwd=PACKAGE, check=True)
    for name, identity in manifest["files"].items():
        actual = hashlib.sha256((PACKAGE / name).read_bytes()).hexdigest()
        if actual != identity["after"]:
            raise SystemExit(f"FAIL: integration compatibility source mismatch: {name}")
    return manifest


if __name__ == "__main__":
    result = prepare()
    print(f"Prepared integration proof compatibility ({len(result['files'])} source files)")
