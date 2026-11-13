import «section 4».RVFiniteBalancedTensor
import «section 4».RVBoundedBalancedTensor
import «section 4».RVMeasuredSpecialClasses
import «section 4».RVRadiusTensor

/-! Actual P, h and radius preimages and values in the tensors balanced
over the intrinsic finite-Gamma ring. Global RV descent remains open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBalancedSpecialClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pPreimage (B : Base (M := M)) : RVFiniteBalancedTensor.Source B :=
  RVFiniteBalancedTensor.fromInteger B (RVMeasuredSpecialClasses.pPreimage B)

def hPreimage (B : Base (M := M)) : RVFiniteBalancedTensor.Source B :=
  RVFiniteBalancedTensor.fromInteger B (RVMeasuredSpecialClasses.hPreimage B)

def radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ GammaRVLifts.admissibleRadii B) :
    RVBoundedBalancedTensor.Source B := RVBoundedBalancedTensor.fromInteger B (RVRadiusTensor.pGammaPreimage B γ hγ)

theorem comparison_pPreimage (B : Base (M := M)) :
    RVFiniteBalancedTensor.comparison B (pPreimage B) = RVMeasuredSpecialClasses.pClass B :=
  (DFunLike.congr_fun (RVFiniteBalancedTensor.comparison_fromInteger B) (RVMeasuredSpecialClasses.pPreimage B)).trans
    (RVMeasuredSpecialClasses.comparison_pPreimage B)

theorem comparison_hPreimage (B : Base (M := M)) :
    RVFiniteBalancedTensor.comparison B (hPreimage B) = RVMeasuredSpecialClasses.hClass B :=
  (DFunLike.congr_fun (RVFiniteBalancedTensor.comparison_fromInteger B) (RVMeasuredSpecialClasses.hPreimage B)).trans
    (RVMeasuredSpecialClasses.comparison_hPreimage B)

theorem comparison_radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ GammaRVLifts.admissibleRadii B) :
    RVBoundedBalancedTensor.comparison B (radiusPreimage B γ hγ) = RVRadiusIdeal.pGamma B γ hγ :=
  (DFunLike.congr_fun (RVBoundedBalancedTensor.comparison_fromInteger B) (RVRadiusTensor.pGammaPreimage B γ hγ)).trans
    (RVRadiusTensor.comparison_pGammaPreimage B γ hγ)

theorem evaluation_pPreimage (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k (pPreimage B) = 0 :=
  (DFunLike.congr_fun (RVFiniteBalancedTensor.evaluation_fromInteger h00 linear hκ hs B hr hγ hΓ k)
    (RVMeasuredSpecialClasses.pPreimage B)).trans (RVMeasuredSpecialClasses.evaluation_pPreimage h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_hPreimage_geometric (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (hPreimage B) = RESMeasuredReduction.pointClass B :=
  (DFunLike.congr_fun (RVFiniteBalancedTensor.evaluation_fromInteger h00 linear hκ hs B hr hγ hΓ EulerKind.geometric)
    (RVMeasuredSpecialClasses.hPreimage B)).trans (RVMeasuredSpecialClasses.evaluation_hPreimage_geometric h00 linear hκ hs B hr hγ hΓ)

theorem evaluation_hPreimage_bounded (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (hPreimage B) = 0 :=
  (DFunLike.congr_fun (RVFiniteBalancedTensor.evaluation_fromInteger h00 linear hκ hs B hr hγ hΓ EulerKind.bounded)
    (RVMeasuredSpecialClasses.hPreimage B)).trans (RVMeasuredSpecialClasses.evaluation_hPreimage_bounded h00 linear hκ hs B hr hγ hΓ)

theorem evaluation_radiusPreimage (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ GammaRVLifts.admissibleRadii B) :
    RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k (radiusPreimage B γ hγ') = 0 :=
  (DFunLike.congr_fun (RVBoundedBalancedTensor.evaluation_fromInteger hc h00 linear hκ hs B hr hγ hΓ k)
    (RVRadiusTensor.pGammaPreimage B γ hγ')).trans (RVRadiusTensor.evaluation_pGammaPreimage hc h00 linear hκ hs B hr hγ hΓ k γ hγ')

end DiamondIntegral.Section4.RVBalancedSpecialClasses
