#!/usr/bin/env python3
"""Build a review PDF for a proposal batch in this folder.

    python3 build-review.py <batch> <build-dir> <tectonic-cache>

Same batch format and colouring as Section7/make-review.py (orange proposed
text in manuscript context), reading the manuscript of this repository. The
compiled extract is written into the batch folder; the build directory and the
tectonic cache are scratch locations given on the command line.
"""
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parents[2]
source = root / 'section 2/reference/diamond_integral_revision_annotated.tex'
TECTONIC = '/Applications/ChatGPT.app/Contents/Resources/tectonic/tectonic'
EXTRACT = Path('/Users/yimu/Documents/Codex-Migration-20261112/projects/diamond integral/Section7/extract-pages.js')
PREAMBLE = r'''
% Review copy only: proposed text is dark orange.
\definecolor{SectionSevenReview}{RGB}{175,75,0}
'''


def load(batch):
    path = here / batch / 'proposal.py'
    spec = importlib.util.spec_from_file_location('proposal', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def edited(text, proposal):
    spans = []
    for edit in proposal.EDITS:
        start, end, new = edit[:3]
        if text.count(start) != 1:
            raise SystemExit(f'Start marker occurs {text.count(start)} times: {start[:80]}')
        a = text.index(start)
        b = text.index(end, a) + len(end)
        spans.append((a, b, new))
    spans.sort()
    for (a1, b1, _), (a2, _, _) in zip(spans, spans[1:]):
        if a2 < b1:
            raise SystemExit('Overlapping edit regions')
    for a, b, new in reversed(spans):
        text = text[:a] + '\\begingroup\\color{SectionSevenReview}' + new + '\\endgroup{}' + text[b:]
    return text


def main(batch, build, cache):
    proposal = load(batch)
    text = edited(source.read_text(), proposal)
    text = text.replace(r'\begin{document}', PREAMBLE + r'\begin{document}', 1)
    build = Path(build)
    build.mkdir(parents=True, exist_ok=True)
    for extra in source.parent.iterdir():
        if extra.suffix in {'.bib', '.bst', '.sty', '.tex'} and extra.name != source.name:
            (build / extra.name).write_bytes(extra.read_bytes())
    (build / 'main.tex').write_text(text)
    env = dict(os.environ, TECTONIC_CACHE_DIR=str(cache))
    result = subprocess.run([TECTONIC, '--only-cached', '--keep-logs', 'main.tex'], cwd=build,
                            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (build / 'compile.out').write_text(result.stdout)
    if result.returncode != 0:
        raise SystemExit('Compilation failed; see ' + str(build / 'compile.out'))
    out = here / batch / f'section7-{batch}-review.pdf'
    pages = subprocess.check_output(['osascript', '-l', 'JavaScript', str(EXTRACT), str(build / 'main.pdf'),
                                     str(out), proposal.TITLE, *proposal.ANCHORS], text=True).strip()
    log = (build / 'main.log').read_text(errors='replace')
    print(json.dumps({'review_pdf': str(out), 'pages': json.loads(pages),
                      'undefined_references': sorted(set(re.findall(r"Reference `([^']+)' on page", log)))},
                     indent=2))


if __name__ == '__main__':
    main(*sys.argv[1:4])
