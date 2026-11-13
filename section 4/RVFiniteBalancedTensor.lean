import «section 4».FiniteGammaAlgebras
import «section 4».RESAllFiniteBalancing
import «section 4».RVMeasuredTensor

/-! The actual measured product comparison and evaluation on the tensor
over the intrinsic finite-Gamma ring. No tensor injectivity, surjectivity
or global RV descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVFiniteBalancedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) :=
  RESChartRing.Ring B ⊗[GammaFiniteRVPresentation.ChartRing B] GammaRVChartPresentation.ChartRing B

def resComparison (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVChartRing.Ring B where
  toRingHom := RVChartMaps.ofRES B
  commutes' _ := rfl

def gammaComparison (B : Base (M := M)) :
    GammaRVChartPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVChartRing.Ring B where
  toRingHom := RVSharpRingMap.sharp B
  commutes' c := (RingHom.congr_fun (GammaFiniteRVMaps.sharp_full_comparison B) c).symm

def comparison (B : Base (M := M)) : Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVChartRing.Ring B :=
  Algebra.TensorProduct.lift (resComparison B) (gammaComparison B) (fun _ _ => Commute.all _ _)

theorem comparison_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) = RVChartMaps.ofRES B x * RVSharpRingMap.sharp B y := rfl

def resEvaluation (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESMeasuredReduction.ReducedRing B where
  toRingHom := RESMeasuredReduction.quotient B
  commutes' _ := rfl

def gammaEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaRVChartPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESMeasuredReduction.ReducedRing B where
  toRingHom := (GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom
  commutes' c := (RESAllFiniteBalancing.finite_balance_apply h00 linear hκ hs B hr hγ hΓ k c).symm

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESMeasuredReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (resEvaluation B) (gammaEvaluation h00 linear hκ hs B hr hγ hΓ k) (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESMeasuredReduction.quotient B x * GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k y := rfl

def resInclusion (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] Source B := Algebra.TensorProduct.includeLeft

def gammaInclusion (B : Base (M := M)) :
    GammaRVChartPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] Source B := Algebra.TensorProduct.includeRight

-- Match RingHom.toIntAlgHom when comparing with the integer tensor.
instance (priority := 1100) sourceIntAlgebra (B : Base (M := M)) : Algebra ℤ (Source B) := Ring.toIntAlgebra (Source B)

instance sourceIntScalarTower (B : Base (M := M)) : IsScalarTower ℤ ℤ (Source B) where
  smul_assoc a b x := by
    change (a * b) • x = a • (b • x)
    exact mul_smul a b x

def fromInteger (B : Base (M := M)) : RVMeasuredTensor.Source B →ₐ[ℤ] Source B :=
  Algebra.TensorProduct.lift (resInclusion B).toRingHom.toIntAlgHom (gammaInclusion B).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem fromInteger_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    fromInteger B (x ⊗ₜ[ℤ] y) = x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y := by
  change (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) * (1 ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem comparison_fromInteger (B : Base (M := M)) :
    (comparison B).toRingHom.toIntAlgHom.comp (fromInteger B) = RVMeasuredTensor.comparison B := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change comparison B (fromInteger B (x ⊗ₜ[ℤ] y)) = RVMeasuredTensor.comparison B (x ⊗ₜ[ℤ] y)
  rw [fromInteger_tmul, comparison_tmul, RVMeasuredTensor.comparison_tmul]

theorem evaluation_fromInteger (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.toIntAlgHom.comp (fromInteger B) =
      RVMeasuredTensor.evaluation h00 linear hκ hs B hr hγ hΓ k := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change evaluation h00 linear hκ hs B hr hγ hΓ k (fromInteger B (x ⊗ₜ[ℤ] y)) =
    RVMeasuredTensor.evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[ℤ] y)
  rw [fromInteger_tmul, evaluation_tmul, RVMeasuredTensor.evaluation_tmul]

theorem comparison_res (B : Base (M := M)) (x : RESChartRing.Ring B) :
    comparison B (resInclusion B x) = RVChartMaps.ofRES B x := by
  change comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [comparison_tmul, map_one, mul_one]

theorem evaluation_res (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (resInclusion B x) = RESMeasuredReduction.quotient B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [evaluation_tmul, map_one, mul_one]

end DiamondIntegral.Section4.RVFiniteBalancedTensor
