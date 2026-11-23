#!/usr/bin/env python3
"""Produce the clean paper from the annotated working manuscript.

    python3 paper/make_clean.py            # writes paper/bounded-integral-motivic-milnor-fiber.tex
    python3 paper/make_clean.py --check    # also fails if any annotation material is left

The annotated manuscript (section 2/reference/diamond_integral_revision_annotated.tex) stays the
working source and the record of the review. This script removes, and changes nothing else:

- every block between "% BEGIN REFEREE INSERTION ..." and "% END REFEREE INSERTION ..." (the
  referee overview, the referee macros in the preamble, the page break before the table of
  contents, and all referee remarks with their resolution notes);
- every block between "% BEGIN AUTHOR RESOLUTION ..." and "% END AUTHOR RESOLUTION ...";
- the \\label{review:...} markers used to delimit review extracts;
- the colour of the one passage of main text set in the resolution colour (the text is kept);
- the authors' working note \\yimu{revision of the next few lemmas} and the two unused note
  macros \\arthur and \\yimu.

A block that was inserted inside a paragraph (no blank line after it) is removed together with
the blank lines before it, so that the sentence or the display that follows continues the
paragraph, as in the text before the annotations were inserted.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'section 2/reference/diamond_integral_revision_annotated.tex'
TARGET = ROOT / 'paper/bounded-integral-motivic-milnor-fiber.tex'

BEGIN = re.compile(r'^% BEGIN (REFEREE INSERTION|AUTHOR RESOLUTION)\b')
END = re.compile(r'^% END (REFEREE INSERTION|AUTHOR RESOLUTION)\b')


def strip_blocks(lines):
    out = []
    i = 0
    removed = 0
    while i < len(lines):
        if BEGIN.match(lines[i]):
            j = i
            while not END.match(lines[j]):
                j += 1
                if j >= len(lines):
                    raise SystemExit(f'Unclosed block starting at line {i + 1}')
                if j > i and BEGIN.match(lines[j]):
                    raise SystemExit(f'Nested block at line {j + 1}')
            removed += 1
            continues = j + 1 < len(lines) and lines[j + 1].strip() != ''
            if continues:
                # The block interrupted a paragraph: drop the blank lines before it.
                while out and out[-1].strip() == '':
                    out.pop()
            i = j + 1
            continue
        out.append(lines[i])
        i += 1
    return out, removed


def main():
    text = SOURCE.read_text()
    lines, removed = strip_blocks(text.split('\n'))
    text = '\n'.join(lines)

    # Review-extract markers.
    # A marker on a line of its own goes with its line; one at the end of a line of text goes alone.
    text, n_own = re.subn(r'(?m)^\\label\{review:[^}]*\}\n', '', text)
    text, n_inline = re.subn(r'[ \t]*\\label\{review:[^}]*\}', '', text)
    n_labels = n_own + n_inline

    # The one passage of main text in the resolution colour: keep the text, drop the colour.
    start = r'{\color{ResolutionGreen}If disc parameters have previously been named,'
    end = r'Without disc parameters, the following argument applies.}'
    if text.count(start) != 1 or text.count(end) != 1:
        raise SystemExit('Coloured passage not found exactly once')
    text = text.replace(start, 'If disc parameters have previously been named,')
    text = text.replace(end, r'Without disc parameters, the following argument applies.')

    # The authors' working note and the two note macros.
    note = '\\yimu{revision of the next few lemmas}\n'
    if text.count(note) != 1:
        raise SystemExit('Working note not found exactly once')
    text = text.replace(note, '')
    for macro in ('\\newcommand{\\arthur}[1]{{\\color{red}#1}}\n', '\\newcommand{\\yimu}[1]{{\\color{blue}#1}}\n'):
        if text.count(macro) != 1:
            raise SystemExit('Note macro not found exactly once: ' + macro.strip())
        text = text.replace(macro, '')

    # At most two consecutive blank lines.
    text = re.sub(r'\n{4,}', '\n\n\n', text)

    live = '\n'.join(l for l in text.split('\n') if not l.lstrip().startswith('%'))
    left = [w for w in ('RefereeRemark', 'REFEREE INSERTION', 'AUTHOR RESOLUTION', 'ResolutionGreen', 'RefereePurple',
                        'SectionFourReview', 'review:', 'Author resolution', '\\yimu{', '\\arthur{')
            if w in (text if w.isupper() else live)]
    TARGET.write_text(text)
    print(f'{removed} blocks and {n_labels} review labels removed; {len(text.splitlines())} lines written to {TARGET.relative_to(ROOT)}')
    if left:
        print('Annotation material left:', left)
        if '--check' in sys.argv:
            raise SystemExit(1)


if __name__ == '__main__':
    main()
