import «section 4».Section3LinkedRetractionStatements
import «section 5».GammaQEFiniteLaws

/-! Propositions 4.7 and 4.15 without the unary Γ rational-affine input:
that input is the theorem `Section5.GammaQE.gamma_piecewise_rational_affine`,
proved from RV quantifier elimination with no further hypotheses. The
statements are otherwise those of `Section3LinkedRetractionStatements`. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.Section3LinkedRetractionStatements
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hc h00 hκ hs hr hγ hΓ

theorem proposition_4_7_discharged :
    ∃ E_g E_b : GradedRingHom (RVGrading.gradedPiece B) (RESReductionGradings.measuredPiece B),
      E_g ≠ E_b ∧
      E_g (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      E_b (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      (∀ x : RESChartRing.Ring B,
        E_g (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x ∧
        E_b (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x) ∧
      E_g (RVMeasuredSpecialClasses.hClass B) = RESMeasuredReduction.pointClass B ∧
      E_b (RVMeasuredSpecialClasses.hClass B) = 0 :=
  proposition_4_7 hc h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ

theorem proposition_4_15_discharged :
    ∃ E : GradedRingHom (RVBoundedGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B),
      RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker E.toRingHom ∧
      ∀ x : RESChartRing.Ring B,
        E (RVBoundedMaps.ofRES B x) = RESOrdinaryReduction.forget B x :=
  proposition_4_15 hc h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ

end DiamondIntegral.Section4.Section3LinkedRetractionStatements
