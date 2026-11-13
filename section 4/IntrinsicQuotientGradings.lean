import «section 4».CoactionQuotientEquivalence
import «section 4».IntrinsicPresentationGradings
import «section 4».RVDisjointRadiusQuotient
import «section 4».RVDisjointPQuotients
import «section 4».RESDisjointReduction

/-! Full gradings on the intrinsic homogeneous P and RES reductions.
Their quotient equivalences preserve degrees in both directions, as does
the bounded radius quotient equivalence. The ordinary P=1 quotient is
inhomogeneous and is not assigned a grading here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.IntrinsicQuotientGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace MeasuredP
open RVDisjointPQuotients.Measured

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ pIdeal B →
    ((RVDisjointGrading.gradingCoaction B).map x).coeff n ∈ pIdeal B :=
  CoactionQuotientEquivalence.ideal_coefficients_of_map (RVDisjointGrading.gradingCoaction B) (RVGrading.gradingCoaction B) (RVDisjointPresentation.equivalence B)
    (pIdeal B) (RVMeasuredPQuotient.pIdeal B) (map_pIdeal B).symm (RVDisjointGrading.toChart_coaction B) (RVMeasuredPQuotient.ideal_coefficients B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVDisjointGrading.gradingCoaction B).quotient (pIdeal B) (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVDisjointPresentation.Ring B} (hx : x ∈ RVDisjointGrading.piece B n) :
    quotient B x ∈ piece B n := (RVDisjointGrading.gradingCoaction B).quotient_mem _ (ideal_coefficients B) hx

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RVMeasuredPQuotient.piece B n ↔ x ∈ piece B n :=
  CoactionQuotientEquivalence.mem_iff (RVDisjointGrading.gradingCoaction B) (RVGrading.gradingCoaction B) (RVDisjointPresentation.equivalence B)
    (pIdeal B) (RVMeasuredPQuotient.pIdeal B) (ideal_coefficients B) (RVMeasuredPQuotient.ideal_coefficients B) (map_pIdeal B).symm
    (fun _ _ hy => RVDisjointGrading.toChart_mem B hy) (fun _ _ hy => IntrinsicPresentationGradings.rvFull_inverse_mem B hy) n x

end MeasuredP

namespace MeasuredRES
open RESDisjointReduction.Measured

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ reductionIdeal B →
    ((RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)).map x).coeff n ∈ reductionIdeal B :=
  CoactionQuotientEquivalence.ideal_coefficients_of_map (RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)) (RESGrading.gradingCoaction B) (RESDisjointPresentation.equivalence B)
    (reductionIdeal B) (RESMeasuredReduction.reductionIdeal B) (map_reductionIdeal B).symm (RESDisjointGrading.toChart_coaction B) (RESReductionGradings.measured_ideal_coefficients B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)).quotient (reductionIdeal B) (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESDisjointPresentation.Ring B} (hx : x ∈ RESDisjointGrading.piece B n) :
    quotient B x ∈ piece B n := (RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)).quotient_mem _ (ideal_coefficients B) hx

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RESReductionGradings.measuredPiece B n ↔ x ∈ piece B n :=
  CoactionQuotientEquivalence.mem_iff (RVFamilyDisjointGrading.gradingCoaction (RESDisjointPresentation.family B)) (RESGrading.gradingCoaction B) (RESDisjointPresentation.equivalence B)
    (reductionIdeal B) (RESMeasuredReduction.reductionIdeal B) (ideal_coefficients B) (RESReductionGradings.measured_ideal_coefficients B) (map_reductionIdeal B).symm
    (fun _ _ hy => RESDisjointGrading.toChart_mem B hy) (fun _ _ hy => IntrinsicPresentationGradings.res_inverse_mem B hy) n x

end MeasuredRES

namespace OrdinaryRES
open RESDisjointReduction.Ordinary

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ fibreIdeal B →
    ((RVOrdinaryFamilyGrading.gradingCoaction (RESOrdinaryDisjointPresentation.family B)).map x).coeff n ∈ fibreIdeal B :=
  CoactionQuotientEquivalence.ideal_coefficients_of_map (RVOrdinaryFamilyGrading.gradingCoaction (RESOrdinaryDisjointPresentation.family B)) (RESOrdinaryGrading.gradingCoaction B) (RESOrdinaryDisjointPresentation.equivalence B)
    (fibreIdeal B) (RESOrdinaryReduction.fibreIdeal B) (map_fibreIdeal B).symm (RESOrdinaryDisjointGrading.toChart_coaction B) (RESReductionGradings.ordinary_ideal_coefficients B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVOrdinaryFamilyGrading.gradingCoaction (RESOrdinaryDisjointPresentation.family B)).quotient (fibreIdeal B) (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryDisjointPresentation.Ring B} (hx : x ∈ RESOrdinaryDisjointGrading.piece B n) :
    quotient B x ∈ piece B n := (RVOrdinaryFamilyGrading.gradingCoaction (RESOrdinaryDisjointPresentation.family B)).quotient_mem _ (ideal_coefficients B) hx

theorem inverse_mem (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryRing.Ring B}
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B n) : (RESOrdinaryDisjointPresentation.equivalence B).symm x ∈ RESOrdinaryDisjointGrading.piece B n := by
  have hi := RingPresentationTransport.inverse_eq (RESOrdinaryDisjointPresentation.equivalence B) (RESOrdinaryDisjointPresentation.fromChartRing B) (RESOrdinaryDisjointPresentation.to_from B)
  change (RESOrdinaryDisjointPresentation.equivalence B).symm.toRingHom x ∈ RESOrdinaryDisjointGrading.piece B n
  rw [hi]
  exact RESOrdinaryDisjointGrading.fromChart_mem B hx

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RESReductionGradings.ordinaryPiece B n ↔ x ∈ piece B n :=
  CoactionQuotientEquivalence.mem_iff (RVOrdinaryFamilyGrading.gradingCoaction (RESOrdinaryDisjointPresentation.family B)) (RESOrdinaryGrading.gradingCoaction B) (RESOrdinaryDisjointPresentation.equivalence B)
    (fibreIdeal B) (RESOrdinaryReduction.fibreIdeal B) (ideal_coefficients B) (RESReductionGradings.ordinary_ideal_coefficients B) (map_fibreIdeal B).symm
    (fun _ _ hy => RESOrdinaryDisjointGrading.toChart_mem B hy) (fun _ _ hy => inverse_mem B hy) n x

end OrdinaryRES

theorem radius_equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : RVDisjointRadiusQuotient.Ring B) :
    RVDisjointRadiusQuotient.quotientEquivalence B x ∈ RVRadiusQuotient.piece B n ↔
      x ∈ RVDisjointRadiusQuotient.piece B n :=
  CoactionQuotientEquivalence.mem_iff
    (RVFamilyDisjointGrading.gradingCoaction (RVBoundedDisjointPresentation.family B))
    (RVBoundedGrading.gradingCoaction B) (RVBoundedDisjointPresentation.equivalence B)
    (RVDisjointRadiusQuotient.radiusIdeal B) (RVRadiusIdeal.radiusIdeal B)
    (RVDisjointRadiusQuotient.ideal_coefficients B) (RVRadiusQuotient.ideal_coefficients B)
    (RVDisjointRadiusQuotient.map_radiusIdeal B).symm
    (fun _ _ hy => RVBoundedDisjointGrading.toChart_mem B hy)
    (fun _ _ hy => IntrinsicPresentationGradings.rvBounded_inverse_mem B hy) n x

end DiamondIntegral.Section4.IntrinsicQuotientGradings
