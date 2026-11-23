# Blueprint

This blueprint follows Forey–Yin, *Bounded integral and motivic Milnor fiber*, in its final form
in this repository ([`paper/bounded-integral-motivic-milnor-fiber.pdf`](../paper/bounded-integral-motivic-milnor-fiber.pdf)),
and links its numbered results to the Lean formalization. Sections and numbers are the paper's.
Each node is one numbered item: every definition, lemma, proposition, theorem and corollary, and
every notation, terminology, convention or remark that a later statement uses or that makes a
mathematical claim; six expository items are left out (listed in the blueprint's introduction).
Three further nodes are the explicit hypotheses of the Lean theorems (the Reichstein–Youssin
consequence, the étale chart and the étale coordinates). Each node has a status (formalized,
partial, not formalized); the reason for each partial or unformalized one cites the decision
recorded in [`FINAL-CHECK.md`](../FINAL-CHECK.md) or the section records.

## Files

- `nodes.json`: the registry. One entry per node: paper number and label, statement, proof
  outline, dependencies, formalization status and note, and the Lean declarations with their
  anchors (provider, file, line).
- `sections.json`: the section titles and introductions.
- `src/content.tex` and `src/source-links.tsv` are generated from these two files; do not edit
  them by hand.
- `proof-source-manifest.json`: the revision the source links point to, the provider pins, and
  fingerprints of the paper, the section receipts and the dependency manifests.
- `scripts/check.py`: validation and regeneration; `scripts/lean_anchors.py`: the declaration
  index of this repository and its providers.

## Build and check

The declaration index reads the Lean sources of this repository and of the five providers at
their pinned revisions (hilbert-mathlib, Fubini-theorems, integration-in-ACVF,
special-transformations, ACVF-QE). In a checkout that has been built they are in
`.lake/packages`; otherwise clone them there at the revisions of `lake-manifest.json` (as the
workflow does), or point `BLUEPRINT_PACKAGES` at a directory holding them. Then, with Python,
Graphviz and its development headers available, at the repository root:

```sh
python -m pip install -r blueprint/requirements.txt
python blueprint/scripts/check.py
leanblueprint web
python blueprint/scripts/check.py --rendered
```

Open `blueprint/web/index.html` and select **Open the theorem dependency graph**. The print
version is `src/print.tex` (`leanblueprint pdf`, or any LaTeX engine run in `src`).

After an edit of `nodes.json` or `sections.json`, or a change of the Lean sources, run
`python blueprint/scripts/check.py --write` to regenerate the TeX and the links and to refresh
the anchors and fingerprints; `--revision <commit>` moves the links to a new pushed commit. The
check fails when a declaration has moved, is in no section receipt, or when the Lean sources differ
from the linked revision.

The workflow `.github/workflows/blueprint.yml` runs these steps on GitHub and publishes the site
with GitHub Pages once Pages is enabled for the repository (source: GitHub Actions).

## Reuse and attribution

The scaffolding, the clickable graph helper and the validation approach are adapted from the
MIT-licensed blueprints of [Fubini-theorems](https://github.com/daviddhilbert/Fubini-theorems/tree/main/blueprint)
and [ACVF-QE](https://github.com/daviddhilbert/ACVF-QE/tree/main/blueprint), which credit the
special-transformations blueprint; `src/dependency_graph.py` keeps its MIT notice. The renderer
is Patrick Massot's `leanblueprint` 0.0.20. The mathematical source authors are Arthur Forey and
Yimu Yin. The statements and proof outlines (`nodes.json`, `sections.json`, `src/content.tex`)
are reproduced from their paper and, like it, are not covered by the repository's Apache-2.0
licence (see the repository README); the scripts and scaffolding are.
