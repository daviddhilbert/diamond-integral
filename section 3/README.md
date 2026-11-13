# Section 3

The active manuscript is the section 2 annotated revision. The four
reviewed §3 referee corrections and the author-initiated T001 correction
are approved and applied. The corrected Proposition 3.18 now states both
positive kernel congruences and graded quotient isomorphisms, with both
proofs. The author-approved C002 proof of the horizontal positive
monomorphisms is also incorporated, with the published Reichstein--Youssin
citation. Review and adoption records are under
`reference/proposed-revisions`. C001's unnecessary alternative reading is
withdrawn. Both ordinary horizontal positive monomorphisms are now proved locally,
including every degree and finite tagged family. All ACVF bridges,
original-ground coefficient recovery and full RV lift gluing are proved;
the approved R--Y classification remains an explicit replaceable input.
Both statements of Remark 3.15 now also have local full-ground proofs. No HK result is a given input.

The formalization entry point is `Section.lean`. Use `verify.py` with the
pinned toolchain to build the whole project, print the actual exported
statements and definitions, and audit their logical principles.

The formalization is complete in the documented paper contexts relative
to the accepted cited-input records. The latest full-ground build/audit
covers 1,003 supporting modules and 5,324 declarations. The separate
[paper-target review](verification/paper-targets.json) checks 21 manuscript
targets against 119 actual declarations and records all scope boundaries.
The later [18] geometric kernels and approved R--Y classification are
explicit inputs; no HK result is assumed. The source manuscript and its
approved PDF remain unchanged.

See [STATUS.md](STATUS.md), [TARGETS.md](TARGETS.md), and
[verification/TYPE-REVIEW.md](verification/TYPE-REVIEW.md) for the semantic
review, hypotheses and verification history. Concrete §4 constructions
and independent disc-name extensions are outside this §3 certificate.


The November 12 dependency refresh links exact section 6 exports at
7d4acc730496b3bd05a22c268ffd89540ca694f9. Their unfinished 5.8 input and
closure/category boundaries are explicit in `verification/integration-reuse.json`;
legacy lift records are not silently replaced. The supplementary unary-ray
refinement was skipped by author instruction. CI prepares both compatibility
patches and audits both sections.
