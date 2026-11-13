import «section 4».Section3T001Integration
import «section 4».RVT001RetractionStatements

/-! The numbered Section 4 retraction statements linked directly to the
finalized Section 3 kernel proofs. General rational-affine Gamma QE
background remains explicit; no T001 interface is an input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.Section3LinkedRetractionStatements
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hc h00 linear hκ hs hr hγ hΓ


theorem proposition_4_7 :
    ∃ E_g E_b : GradedRingHom (RVGrading.gradedPiece B) (RESReductionGradings.measuredPiece B),
      E_g ≠ E_b ∧
      E_g (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      E_b (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      (∀ x : RESChartRing.Ring B,
        E_g (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x ∧
        E_b (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x) ∧
      E_g (RVMeasuredSpecialClasses.hClass B) = RESMeasuredReduction.pointClass B ∧
      E_b (RVMeasuredSpecialClasses.hClass B) = 0 :=
  RVT001RetractionStatements.proposition_4_7 hc h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.measured (hc := hc) hκ hs h00 hr hγ hΓ)

theorem proposition_4_15 :
    ∃ E : GradedRingHom (RVBoundedGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B),
      RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker E.toRingHom ∧
      ∀ x : RESChartRing.Ring B,
        E (RVBoundedMaps.ofRES B x) = RESOrdinaryReduction.forget B x :=
  RVT001RetractionStatements.proposition_4_15 h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)

end DiamondIntegral.Section4.Section3LinkedRetractionStatements
