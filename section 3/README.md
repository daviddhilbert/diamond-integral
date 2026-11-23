# Section 3

All four Gamma-valued measured input records now have local proved producers,
including the original-base positive-degree reverse kernel. See
[the completion note](verification/GAMMA-KERNEL-COMPLETION.md) and
[verification progress](verification/GAMMA-EXTENSION-PROGRESS.json).

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
to the approved R--Y classification. The latest build/audit (November 18,
PASS) covers 1,527 supporting modules, 3,895 public theorems and 2,806
printed definitions. The separate
[paper-target review](verification/paper-targets.json) checks 21 manuscript
targets against 132 declaration links and records all scope boundaries.
The later [18] lift/kernel records are now all produced: Gamma-ground
unmeasured by `Section5.completed18GroundLiftInput`, bounded by
`completedGammaGroundBoundedLiftInput` (headline `theorem_3_22_bounded`),
ordinary bounded by `MeasuredRealGround.completedOrdinaryBoundedLiftInput`,
and the measured records by local proofs. Theorem 3.22's graded measured
isomorphism is `theorem_3_22_measured_graded`, and Remark 3.14 is
`remark_3_14` (with `_converse`, `_point`). The section 2 inputs are
discharged in `Section2CitedInputsDischarged.lean` and
`Section2GammaLinearityDischarged.lean`. November 17–18 work and the
author-approved "not pursued" items are in [GAP-REPAIRS.md](GAP-REPAIRS.md).
The approved R--Y classification remains an explicit input; no HK result is
assumed.

See [STATUS.md](STATUS.md), [TARGETS.md](TARGETS.md), and
[verification/TYPE-REVIEW.md](verification/TYPE-REVIEW.md) for the semantic
review, hypotheses and verification history. Concrete §4 constructions
and independent disc-name extensions are outside this §3 certificate.


The current pin is 7238c3863ef7ea65ab3c21bcb0982be4cac9728f (Special
transformations 37e4dfacb293f38db28b2d8eca46a285eead3127; November 23, after the
shared foundations moved to hilbert-mathlib; no public declaration changed). The bounded native integral now uses the closed
`IntegrationInACVF.Section7.CompletedSection6` API of that pin. The November 12
refresh linked exact section 6 exports at 7d4acc730496b3bd05a22c268ffd89540ca694f9,
then relative to an unfinished 5.8 input. That input is now discharged
(`Section5.completed_section5_input`, from the completed upstream Section 5),
and the closure/category transport is compiled in section 5; see
`verification/integration-reuse.json`. The supplementary unary-ray
refinement was skipped by author instruction. CI prepares both compatibility
patches and audits both sections.
