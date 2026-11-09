"""Register sibling modules in the pinned ACVF-QE release.

The release's Proofs directory contains separate top-level modules. Lake
needs those module roots when ACVFQE is built as a dependency. The adjustment
is limited to the dependency's Lake metadata, as in Special Transformations.
"""

import json
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    revision = "f3ef4ee679f921079aa8f742a2807a9cc724d2d6"
    dependency = next(pkg for pkg in manifest["packages"] if pkg["name"] == "acvf_qe")
    package = root / manifest["packagesDir"] / dependency["name"]
    head = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True)
    if dependency["rev"] != revision or head.strip() != revision:
        raise SystemExit("Review the ACVF-QE module layout before changing the pinned revision.")

    modules = sorted(proof.stem for proof in (package / "Proofs").glob("*.lean"))
    if "ACVFQE" not in modules or len(modules) < 2:
        raise SystemExit("Expected the top-level ACVF-QE proof modules.")
    config = package / "lakefile.toml"
    text = config.read_text(encoding="utf-8")
    old = 'roots = ["ACVFQE"]'
    new = "roots = " + json.dumps(modules)
    if new not in text:
        if text.count(old) != 1 or text.count("[[lean_lib]]") != 1:
            raise SystemExit("Unexpected ACVF-QE Lake configuration.")
        config.write_text(text.replace(old, new), encoding="utf-8")
    print(f"Registered {len(modules)} ACVF-QE Lake module roots.")


if __name__ == "__main__":
    main()
