# Bounded integral and motivic Milnor fiber

Lean formalization and annotated manuscript for Forey and Yin's paper.

**Start with [HANDOFF.md](HANDOFF.md)** for the current status of Sections
1–8, the author-approved workflow and exact build instructions. It is written
for an agent continuing in another program from this public repository and
the original PDF/referee report supplied separately by the author.

- [Clean paper](paper/bounded-integral-motivic-milnor-fiber.pdf) ([TeX](paper/bounded-integral-motivic-milnor-fiber.tex)):
  the manuscript without the referee items and resolution notes, generated from the
  working manuscript by `paper/make_clean.py`; every theorem and equation number is the same
- [Working manuscript](<section 2/reference/diamond_integral_revision_annotated.tex>), with the
  referee items and their resolutions (the record of the review)
- [Final check of November 22](FINAL-CHECK.md): the clean paper, the build and receipts, and the
  paper compared with the Lean statements, section by section
- [Project instructions](AGENTS.md)
- [Upstream weighted-degree-zero compatibility audit](UPSTREAM-WEIGHTED-ZERO-AUDIT.md)
- [Section 7 status](<section 7/STATUS.md>) and [receipt](<section 7/verification/status.json>)
- [Section 8 plan](<section 8/PLAN.md>) and [receipt](<section 8/verification/status.json>)
- [Shared-foundation migration verification](verification/shared-foundation.json)
- [Weighted-degree-zero baseline verification](verification/upstream-weighted-zero-upgrade/status.json)
- [Original aperture-revision verification](<section 6/verification/aperture-revision/integrated-audits.json>)

The checked baseline includes completed Sections 2–8 in their recorded
scopes, including revised Definition 6.11, the synchronized Section 7
aperture and kernel assembly (Theorem 7.26 with `J_var`), and Section 8 for
`X = 𝔸^d` and smooth affine `X`. Historical planning notes do not supersede
current coverage maps and receipts. The introduction was reconciled with these
sections on November 22; the Fubini theorems of the former Section 5 are now in
their own paper in the Fubini-theorems repository, and Section 5 of the
manuscript recalls only what Section 8 uses.

The pinned [hilbert-mathlib](https://github.com/daviddhilbert/hilbert-mathlib)
dependency now owns 65 reusable modules formerly implemented here, within the
approved 106-module shared extraction. Their original paths are compatibility
imports; declaration names and mathematical statements are unchanged.
[SHARED-FOUNDATION.json](SHARED-FOUNDATION.json) records exact providers and
source fingerprints. Section verifiers inspect the relocated proof bodies and
check their pinned source identities. Current full audit output is retained in
CI artifacts; the repository's older generated snapshots remain matched
historical checkpoints.

The independent [Fubini-theorems](https://github.com/daviddhilbert/Fubini-theorems)
package owns the active Section 5 development and all its local prerequisites.
It preserves the bounded and geometric Fubini theorems, comparison results,
and variety corollary with their original public names and hypotheses.
This project consumes the pinned package through its original import paths.
[EXTRACTED-FOUNDATIONS.json](EXTRACTED-FOUNDATIONS.json) records the exact
providers for 1,786 Fubini modules and 17 whole-module upstream promotions;
the finite-laws split is recorded as well. Section verifiers follow the
relocated proof bodies, while the Fubini provider checks the 10,566-type
public contract against the pre-extraction baseline.

## Further shared-foundation extraction

The additional extraction places 15 generic implementation files in
hilbert-mathlib, retaining their original import paths and public types.
`SHARED-FOUNDATION.json` now checks 80 direct shared paths. The 48 newly shared
Fubini prerequisite paths in `EXTRACTED-FOUNDATIONS.json` resolve to their
actual hilbert-mathlib proof bodies; the two paper-specific Grothendieck
relations remain in Fubini. Section verifiers continue auditing the provider
implementations and the unchanged mathematical hypotheses.

## License

This repository is licensed under the [Apache License, Version 2.0](LICENSE).

The licence does not cover the paper, which is joint work of Forey and Yin, or
material reproduced from it: the clean paper
`paper/bounded-integral-motivic-milnor-fiber.tex` and its PDF, the annotated manuscript
`section 2/reference/diamond_integral_revision_annotated.tex` and its PDF,
`section 2/reference/original-upload/`, and the PDF and TeX files in the
sections' `reference/` folders. Files from third parties keep their own notices
and licences.
