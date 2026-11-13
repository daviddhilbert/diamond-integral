#!/usr/bin/env python3
"""Recheck the evidence behind DEPENDENCY-AUDIT.md after section updates.

Run from the repository root after activating the project Lean environment.
The separate section verifiers supply the complete library audits; this
check verifies their local proof hashes and the focused boundary types.
"""

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "verification/section-boundaries.json"
LEAN = ROOT / "verification/SectionBoundaryAudit.lean"
OUTPUT = ROOT / "verification/section-boundary-types.txt"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    report = json.loads(RECORD.read_text())
    checks = {}
    for section, receipt in [
        (2, "section 2/verification/status.json"),
        (3, "section 3/verification/VERIFICATION.json"),
    ]:
        data = json.loads((ROOT / receipt).read_text())
        if data["status"] != "PASS":
            raise SystemExit(f"Non-passing section receipt: {receipt}")
        sources = data.get("sources", data.get("source_sha256", {}))
        own = {p: h for p, h in sources.items()
               if p.startswith(f"section {section}/") and p.endswith(".lean")}
        if not own:
            raise SystemExit(f"Missing proof-source hashes: {receipt}")
        mismatches = [p for p, h in own.items()
                      if not (ROOT / p).is_file() or sha(ROOT / p) != h]
        checks[receipt] = {"checked_Lean_sources": len(own), "mismatches": mismatches}
        if mismatches:
            raise SystemExit(f"Stale section proof receipt: {mismatches}")

    names = re.findall(r"^#print (?!axioms )(.+)$", LEAN.read_text(), re.M)
    with OUTPUT.open("w") as output:
        subprocess.run(["lake", "env", "lean", str(LEAN.relative_to(ROOT))],
                       cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=True)
    result = OUTPUT.read_text()
    principles = {}
    for name, raw in re.findall(r"'([^\n]+)' depends on axioms: \[([^\]]*)\]", result):
        used = {a.strip() for a in re.sub(r"\.\{[^}]*\}", "", raw).split(",") if a.strip()}
        used = {"Classical.choice" if a == "choice" else a for a in used}
        if not used <= ALLOWED:
            raise SystemExit(f"Unexpected logical axiom: {name}: {used - ALLOWED}")
        principles[name] = sorted(used)
    for name in re.findall(r"'([^\n]+)' does not depend on any axioms", result):
        principles[name] = []
    if set(names) != set(principles):
        raise SystemExit("Incomplete focused boundary audit")

    report["focused_type_audit"].update(
        status="PASS", declarations=len(names), declaration_principles=principles)
    report["proof_source_hash_checks"] = checks
    count = sum(len(list((ROOT / f"section {i}").rglob("*.lean"))) for i in range(5, 9))
    report["sections5_to_8"]["Lean_files"] = count
    if count:
        report["sections5_to_8"]["status"] = "Implementations present; individual boundary audits required"
    for source in report["sources"]:
        report["sources"][source] = sha(ROOT / source)
    report["sources"][str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    RECORD.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"PASS: {len(names)} boundary types; matching Section 2/3 proof hashes; "
          f"{count} Lean files in Sections 5–8.")


if __name__ == "__main__":
    main()
