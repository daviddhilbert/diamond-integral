# Section 7 — Integrating proper invariant sets

Start with the [full-paper continuation handoff](../HANDOFF.md). It covers
Sections 1–8, the mathematical review and Lean workflow, the approved
Definition 6.11 repair, exact dependency setup and the remaining Section 7
proof obligations. The author will supply the original PDF and referee
report separately; use the adopted annotated TeX for approved revisions.

The §7 main text is already revised for bounded variable apertures and J_var.
The Lean formalization is in progress; see [PLAN.md](PLAN.md) (approved by the
author on 2026-11-19), [STATUS.md](STATUS.md), [COVERAGE.md](COVERAGE.md) and
[GAP-REPAIRS.md](GAP-REPAIRS.md). Complete so far: Definition 7.2 on isomorphism
classes, Lemma 7.5, Corollary 7.6, Lemma 7.7, Corollary 7.8, Definition 7.9,
the additive part of Lemma 7.10, Remark 7.3 (dimension claim), Lemma 7.11 (full
lift, on classes), Lemma 7.12 on classes, Lemma 7.13 (printed form, head start
0; also over a base with adjoined VF parameters), Definitions 7.16, 7.17, 7.19
and Remark 7.18 (approved scope), the surjectivity of the lift on classes, and
Lemma 7.14 (`Lemma714Reduce.lemma714`), Corollary 7.15
(`ProvedResults.corollary_7_15`), Lemma 7.20 (`Lemma720.lemma720`), Lemma 7.21
in the uniform form used by 7.22, Lemma 7.22 (`ProvedResults.lemma_7_22`) and
Lemma 7.23 in every dimension (`Lemma723General.lemma_7_23`). Lemmas 7.14 and 7.20 were
temporary inputs (author decision of 2026-11-19), proved in separate sessions
and merged; `FiberwiseInput.Lemma714` and `TwoCellInput.Lemma720` keep their
statements. Proposition 7.24 (`Proposition724.proposition_7_24`, degree 0 in
`Proposition724Zero`), Remark 7.25 (`Theorem726.remark_7_25`) and Theorem 7.26
(`Proposition724.integralEquiv`, `Theorem726.integralRingEquiv`) are done on the
temporary intermediate-forms input `IntermediateFormsInput.IntermediateForms`
(author decision of 2026-11-20, GAP-REPAIRS 16). That input turned out to be
false as stated for n = 2, so these positive-degree results are not
established; degree 0 is done without it, and the route is the author's
decision. Remaining: the approved partial-lift form of 7.11 and Corollary 7.27.
Remark 7.28 is done (`Remark728`).

The focused [Section 6 handoff](SECTION6-HANDOFF.md) links the checked native
inputs and the mathematical draft. The draft is not a completed kernel
theorem. Old page ranges are historical; identify targets by LaTeX labels
in the [working manuscript](../section%202/reference/diamond_integral_revision_annotated.tex).

Upstream export used in proofs (not as a hypothesis):
`IntegrationInACVF.Section7.lemma_5_2_gamma_presented_without_field`
(integration-in-ACVF, pinned revision `ab4c0e8b15e1e21b0b4fce57eed764be76020e06`,
`section 7/Integration7/UnaryCompatiblePreparationWithoutField.lean`). It is
Yin's unary compatible preparation (Lemma 5.2 of [18]) over a small base
without a VF field base. `SetBaseMatching` uses it in place of
`lemma_5_2_gamma_presented`, so that Lemma 6.38 holds over support data.
