# Lemma 2.11 reuse record

Checked November 9, 2026 with Lean 4.35.0 and the revisions in
`../verification/status.json`. The Special Transformations base revision is
`9cc9760892092dd34cfad4a6dee655843c52f30c`, with the separate author-approved
finite-open-radius patch. No new external source code was copied.

The completed forward implication imports
`SpecialTransformations.Section7.valuationRing_henselian`, which proves the
ordinary Mathlib `HenselianLocalRing` property using the released ACVF-QE
monic root-lifting theorem. Ambient VF algebraic closedness is supplied by
`VFAlgClosed.isAlgClosed_vfType`. Root equations reuse
`Section3.PolynomialRoots.rootSet_definable` over the original coefficient
field. Uniqueness reuses
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` from pinned Mathlib,
attributed there to Stacks Project tag 06RR. The new residue-class formula is
well-sorted in the fixed LRV language and needs only its original centre.

Fresh combined project verification passed with 48 public section theorem
type/axiom audits and 260 selected reuse audits. All audited axioms are among `propext`,
`Classical.choice`, and `Quot.sound`. The exact forward theorem retains ACVF,
a compatible valuation, the VF-field convention, and definable closedness;
it has no assumption of a root-lifting or henselian conclusion.

For the reverse implication, `AlgebraicEnvelope.lean` constructs the elementary
algebraic closure from `canonical_algebraicClosureSubstructure_elementary`,
identifies the original base inside it and proves the Galois property using
Mathlib's `IsAlgClosure`/`IsGalois` interfaces. Henselianity transports through
the identified base fields using
`Section6.HenselianTheory.henselian_of_compatible_equiv`.
`Section6.henselian_automorphism_invariance` discharges the valuation input;
`lemma_6_2_in_algebraic_envelope_pure` then combines the checked VF fixed-field
and RV conjugate-average arguments. `DclClosed.image` descends the result
through the actual elementary embedding. All these imported headlines have
fresh type and axiom audits. The envelope/Galois premises are discharged in
the proof of `lemma_2_11`, not retained as additional headline assumptions.

The representation premise `CanonicalStructure.IsCanonical` fixes off-sort
totalizations in the encoding of the two-sorted language. Transport to arbitrary
off-sort totalizations is not claimed. The original field/RV base and its
nontrivial valuation witness remain visible in the headline. The older
`Section3.VFGenerated` and `GammaParameters.VFGeneratedBase` mean generation
under definable closure, so they cannot be used to represent the unclosed
base of Lemma 2.11. The new `Bases.lean` interface avoids that circularity.
