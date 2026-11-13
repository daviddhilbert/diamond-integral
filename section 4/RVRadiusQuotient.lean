import «section 4».RVRadiusIdeal
import «section 4».PolynomialCoactionQuotient

/-! The actual bounded RV quotient by the accepted radius ideal is graded.
Each radius class vanishes there, including the separate zero-radius case.
No retraction or identification with manuscript categories is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVRadiusQuotient
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def Ring (B : Base (M := M)) := RVBoundedRing.Ring B ⧸ RVRadiusIdeal.radiusIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVBoundedRing.Ring B →+* Ring B :=
  Ideal.Quotient.mk (RVRadiusIdeal.radiusIdeal B)

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ RVRadiusIdeal.radiusIdeal B →
      (RVBoundedGrading.coaction B x).coeff n ∈ RVRadiusIdeal.radiusIdeal B :=
  (RVBoundedGrading.gradingCoaction B).homogeneous_ideal_coefficients _ (RVRadiusIdeal.radiusIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RVBoundedGrading.gradingCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedRing.Ring B}
    (hx : x ∈ RVBoundedGrading.gradedPiece B n) : quotient B x ∈ piece B n :=
  (RVBoundedGrading.gradingCoaction B).quotient_mem _ (ideal_coefficients B) hx

theorem pGamma_zero (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ GammaRVLifts.admissibleRadii B) : quotient B (RVRadiusIdeal.pGamma B γ hγ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (RVRadiusIdeal.pGamma_mem_ideal B γ hγ)

def ofRES (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (quotient B).comp (RVBoundedMaps.ofRES B)

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : ofRES B x ∈ piece B n :=
  quotient_mem B (RVBoundedMaps.ofRES_mem B hx)

end DiamondIntegral.Section4.RVRadiusQuotient
