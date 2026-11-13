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
General rational-affine Gamma QE background remains explicit. Later accepted
external inputs in Section 3 retain their documented scope; no HK input is
introduced. See the [project dependency audit](../DEPENDENCY-AUDIT.md).

The complete Section 4 audit passes 4998 declarations (3027 theorems)
across 600 modules, with only `propext`, `Classical.choice` and `Quot.sound`.

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
  cell refinement are proved locally from rational-affine normal form.
- Remark 4.4: the actual natural affine-localization comparison is proved
  nonsurjective. The affine line is outside its image. The proof uses
  actual RES coordinate covers, uniform finite-fibre bounds and
  finite-diagram point counts over arbitrarily large finite fields.
- Actual degree-one measured point nonvanishing and affine-point
  separation are proved through constructed residue trace maps.
- The unary function rings, convolution, multivariable Euler integration,
  Fubini, invariance, bounded comparison, stabilization, target rings,
  gradings, finite-union presentations and all stated maps are constructed.

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
