#!/usr/bin/env python3
"""Build the working manuscript and extract the current small review batch."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

import fitz

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
REFERENCE = ROOT / "section 2/reference"
SOURCE = REFERENCE / "diamond_integral_revision_annotated.tex"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-label", default="subs:uni:retr:novol")
    parser.add_argument("--end-label", default="review:section4:tensor:end")
    parser.add_argument("--items", nargs="+", default=["R058", "R059"])
    parser.add_argument("--colored-pages-only", action="store_true",
                        help="Extract only pages containing the orange main-text review color")
    parser.add_argument("--basis", help="Record the actual authorization basis for this batch")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--pending", action="store_true")
    mode.add_argument("--accepted", action="store_true")
    args = parser.parse_args()
    if not 1 <= len(args.items) <= 2:
        raise SystemExit("Show at most two review items per batch")
    record_dir = SECTION / "verification"
    record_dir.mkdir(exist_ok=True)
    certificate = record_dir / "manuscript-review.json"
    certificate.unlink(missing_ok=True)
    env = os.environ.copy()
    local_texmf = Path("/workspace/.tools/section4-texmf")
    if not env.get("TEXMFHOME") and local_texmf.is_dir():
        env["TEXMFHOME"] = str(local_texmf)
    with tempfile.TemporaryDirectory(prefix="section4-review-") as scratch:
        scratch = Path(scratch)
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   "-jobname=diamond_integral_revision_annotated",
                   f"-output-directory={scratch}",
                   r"\pdfmapfile{+dstroke.map}\pdfmapfile{+stmaryrd.map}\input{diamond_integral_revision_annotated.tex}"]
        outputs = []
        for _ in range(3):
            result = subprocess.run(command, cwd=REFERENCE, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            outputs.append(result.stdout)
            if result.returncode:
                (record_dir / "manuscript-build.txt").write_text(result.stdout)
                raise SystemExit(result.stdout[-5000:])
        log = (scratch / "diamond_integral_revision_annotated.log").read_text()
        if re.search(r"There were undefined references|Undefined control sequence|(?:Reference|Citation)[^\n]*undefined", log):
            raise SystemExit("Unresolved manuscript references in final build")
        aux = (scratch / "diamond_integral_revision_annotated.aux").read_text()

        def page(label):
            match = re.search(r"\\newlabel\{" + re.escape(label) + r"\}\{\{[^}]*\}\{(\d+)\}", aux)
            if not match:
                raise SystemExit(f"Missing review label: {label}")
            return int(match[1])

        first, last = page(args.start_label), page(args.end_label)
        if last < first:
            raise SystemExit("Review labels have reversed page order")
        pdf = REFERENCE / "diamond_integral_revision_annotated.pdf"
        shutil.copy2(scratch / pdf.name, pdf)
        full = fitz.open(pdf)
        excerpt = fitz.open()
        selected = list(range(first - 1, last))
        if args.colored_pages_only:
            selected = [i for i in selected if any(
                span.get("color") == 0xAF4B00
                for block in full[i].get_text("dict")["blocks"]
                for line in block.get("lines", [])
                for span in line["spans"])]
            if not selected:
                raise SystemExit("No orange main-text review passages found in the selected range")
        for source_page in selected:
            excerpt.insert_pdf(full, from_page=source_page, to_page=source_page)
        for i, source_page in enumerate(selected):
            assert excerpt[i].get_text() == full[source_page].get_text()
        extract_path = SECTION / "reference/section4-main-text-review.pdf"
        excerpt.save(scratch / "extract.pdf", garbage=4, deflate=True)
        shutil.copy2(scratch / "extract.pdf", extract_path)
        patch = SECTION / "reference/section4-colored-main-text.patch"
        patch.write_bytes(subprocess.check_output(
            ["git", "diff", "--", str(SOURCE.relative_to(ROOT))], cwd=ROOT))
        source_text = SOURCE.read_text()
        a = source_text.index(r"\section{Uniform retraction")
        b = source_text.index(r"\section{Interlude:", a)
        record = {
            "status": "PENDING_AUTHOR_DECISION" if args.pending else
                      "APPLIED_AUTHOR_APPROVED" if args.accepted else "APPLIED_CLEAR_CORRECTIONS",
            "current_display_items": args.items, "printed_pages": [first, last],
            "selected_printed_pages": [i + 1 for i in selected],
            "full_pdf_pages": len(full), "approval_requested": args.pending,
            "resolution_basis": args.basis or ("Explicit author approval of the displayed main-text proposal." if args.accepted else
                                "Author standing authorization for independently established clear corrections."),
            "resolved_section4_referee_ids": re.findall(r"\\ResolvedRefereeRemark\{(\d+)\}", source_text[a:b]),
            "unflagged_editorial_fixes": ["epsilon_g^{k,l} to epsilon_g^{n,l}",
                                          "Repair the post-diagram sentence fragment",
                                          "State vanishing for homogeneous positive Gamma degree, not mixed degrees"],
            "deferred_proposals": "section 4/reference/deferred-proposals/",
            "baseline_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "sources": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [SOURCE, pdf, extract_path, patch, Path(__file__).resolve()]},
            "latex": "Three successful pdflatex passes; no unresolved references.",
        }
        certificate.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        (record_dir / "manuscript-build.txt").write_text(
            "Build command: " + repr(command) + "\n"
            + "TEXMFHOME: " + env.get("TEXMFHOME", "system default") + "\n"
            + "Excerpt: exact page-text equality checked against full manuscript.\n"
            + "Final diagnostics:\n"
            + "\n".join(line for line in log.splitlines() if any(
                word in line for word in ["Warning", "Overfull", "Output written"])) + "\n")
        pages = ", ".join(str(i + 1) for i in selected)
        print(f"Built manuscript and {len(excerpt)}-page review extract, printed pp. {pages}: {', '.join(args.items)}")


if __name__ == "__main__":
    main()
