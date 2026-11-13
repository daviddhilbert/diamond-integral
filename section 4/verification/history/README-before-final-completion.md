# Historical progress record

Superseded by the current Section 4 status after the author accepted Section 3 as background.

# Section 4 — Uniform retraction to RES

Original annotated manuscript, pp. 29–35; current pagination is recorded with each review batch.

Build the unmeasured and measured retractions separately. Check the Euler characteristic, convolution, bounded support and the precise quotient in each target.

See the [formalization plan](../FORMALIZATION-PLAN.md) for reuse and verification.

The whole-section inventory is [COVERAGE.md](COVERAGE.md), with current
proof and manuscript status in [STATUS.md](STATUS.md). The author approved
restricting the Pγ generators and their ideal to nonnegative radii with an
S-definable RV lift (R069). This is applied in the
[working manuscript](../section%202/reference/diamond_integral_revision_annotated.tex)
and its [PDF](../section%202/reference/diamond_integral_revision_annotated.pdf).
The accepted [radius extract](reference/section4-radius-accepted.pdf) retains
that passage. The current [focused extract](reference/section4-main-text-review.pdf)
contains the approved kernel-descent and bounded-restriction changes in ordinary text color. The earlier colored copy is preserved as `reference/section4-T001-colored-approved.pdf`. There are no pending author-review questions. Other independently established clear
corrections have been applied directly under the author's standing instruction.

The Lean entry point is `Section.lean`. Run `python3 'section 4/verify.py'`
from the repository root in the activated pinned Lean environment. The unary first-order function rings, bounded quotient and finite-piece
pushforwards are implemented over the original base. Finite-dimensional
coordinate and block Fubini, definable-bijection invariance, products, bounded
comparison and pushforward from Gamma^n to Gamma are also proved, with
explicit hypotheses recorded in STATUS.md. Full gradings on both concrete
RES chart rings and their actual reduction quotients, and compatibility of
the forgetful map with homogeneous components, are proved. The actual graded
category maps and numbered retraction propositions remain unfinished.

T001's approval is confirmed. The actual RV descent proofs now retain
explicit upstream-presentation transport hypotheses; see STATUS.md for
the precise scope and the remaining Lean presentation-transport obligation. The approved Section 3 manuscript statement and both proofs have been synchronized verbatim.


The actual measured degree-one point is now proved nonzero by
`RESPointNonvanishing.lean`. Both main retraction statements, with all
clauses including distinctness, are assembled in
`RVT001RetractionStatements.lean` relative to the explicit corrected
Section 3 presentation transport. The transport adapter itself remains
uninstantiated; this is not an unconditional full-section certification.
