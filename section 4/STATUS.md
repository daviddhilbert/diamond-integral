# Section 4 status

The corrected Section 4 results are complete and directly linked to finalized
Section 3 at commit `37c8361`. Both T001 presentation interfaces are now
constructed from its compiled kernel and surjectivity proofs. No manuscript
change or author decision is pending.

`Section3T001Integration.lean` supplies the actual transport records: ordinary
and measured RES, Gamma, finite-Gamma and RV ring equivalences; coefficient
scalar squares; balanced source tensor equivalences; comparison squares; and
transport of every elementary positive coefficient pair into the chart ideal.
All conversions retain the original base, object degrees, finite family tags,
partial forms and full proper RV preimages. No tensor injectivity is assumed.

`Section3LinkedRetractionStatements.lean` proves Propositions 4.7 and 4.15
without T001 interface inputs. The original modular descent theorems remain
available with explicit interfaces, now inhabited by proved constructors.
The unary rational-affine Gamma input is proved
(`Section5.GammaQE.gamma_piecewise_rational_affine`), and
`Section4GammaLinearityDischarged.lean` gives `proposition_4_7_discharged` and
`proposition_4_15_discharged` without it. The multivariate normal form
`Section3GammaAffineInput.Input`, used by Remark 4.2, remains explicit (known
open). Later accepted external inputs in Section 3 retain their documented
scope; no HK input is introduced. See the
[project dependency audit](../DEPENDENCY-AUDIT.md).

November 17–18 additions (see [GAP-REPAIRS.md](GAP-REPAIRS.md)): Notation 4.17
and Lemma 4.18 for the manuscript ideal J_var (`RelativeAnnular*`, with the
blowup modules moved from section 7), the positive tensor map of Remark 4.10,
the Definition 4.9 ∞-coordinate comparison (`RVStrictBoundedComparison`),
`Section4LinkedRemarks` (diagram (edb:eb:com), Remarks 4.4/4.16) and the
Proposition 3.18 kernel witness (recorded under section 3).

The complete Section 4 audit (November 18) passes 5493 declarations (3340
theorems) across 621 modules plus `Section.lean`, with only `propext`,
`Classical.choice` and `Quot.sound`. The hard-coded summary strings in
`verify.py` (copied into `verification/status.json`) still call the
rational-affine Gamma background accepted; for the unary input this is out
of date.

The approved T001 manuscript statement and both proofs remain verbatim.
Other approved Section 3 manuscript changes are synchronized; the entire
Section 4 main-text body is unchanged. See
[the source and integration audit](verification/final-section3-audit.json).

## Manuscript

All 19 referee items and the approved T001 follow-through are resolved.
The corrected geometric value in Proposition 4.7 is +[1], negative
intervals and the zero-radius case are handled, and both P_gamma and its
ideal use nonnegative radii with original-base definable RV lifts. The
ordinary/measured kernel descent and the bounded construction follow the
approved Section 3 correction. The degree-one point nonvanishing
justification is included in the main text.

The synchronized main PDF has 94 pages. The resolved section extract contains printed
pages 40–48. Three LaTeX passes succeeded with no unresolved references;
each extract page's text equals the corresponding full-manuscript page.
The affected pages were visually checked. The right-panel display request
returned **queued**, so panel visibility is unconfirmed. The approved
colored T001 review copy is preserved separately.

## Proof completion

- Propositions 4.7 and 4.15: all clauses, retraction properties, grading,
  P/h values, distinctness, admissible-radius descent and the bounded
  commuting diagram are proved with compiled Section 3 constructors for both T001 interfaces.
- Remark 4.2: continuous cell decomposition in every finite arity and
  equality of geometric Euler characteristic with the alternating sum
  of the ordinary recursive cell dimensions are proved. Continuity and
  cell refinement are proved locally from the multivariate rational-affine
  normal form, which is still an explicit input.
- Remark 4.4: the actual natural affine-localization comparison is proved
  nonsurjective. The affine line is outside its image. The proof uses
  actual RES coordinate covers, uniform finite-fibre bounds and
  finite-diagram point counts over arbitrarily large finite fields.
- Actual degree-one measured point nonvanishing and affine-point
  separation are proved through constructed residue trace maps.
- The unary function rings, convolution, multivariable Euler integration,
  Fubini, invariance, bounded comparison, stabilization, target rings,
  gradings, finite-union presentations of the graded rings and all stated
  maps are constructed. The identification of the dimension-free RES ring
  with the Grothendieck ring of the dimension-free category under finite
  coproducts is not built.
- Not pursued (author-approved triage, November 18): the explanatory items
  listed in GAP-REPAIRS.md (Notation 4.13's unmeasured ring and inequality,
  K μΓ[0] ≅ ℤ[Γ_def] in Remark 4.6, parts of Remark 4.4, the second
  paragraph of Remark 4.16, Remark 4.10's first sentence).

The corrected main text asserts a natural affine comparison. Formalizing
the referee's particular counterexample varieties to the removed
injectivity claim is not part of that main-text obligation.

Exact theorem locations are in [COVERAGE.md](COVERAGE.md). The verifier
prints complete declaration types and logical dependencies, including the
explicit background definitions. No HK theorem is an input. Original-base
smallness, ACVF(0,0), canonical/saturation hypotheses where used, and the
approved nontrivial Gamma convention are retained. A definable Gamma value
is never silently promoted to a definable RV lift.

Earlier implementation entries are preserved under `verification/history/`.
The author authorized committing and pushing the completed work after the audits.
