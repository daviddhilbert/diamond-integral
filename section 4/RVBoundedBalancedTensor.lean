import «section 4».FiniteGammaAlgebras
import «section 4».RESAllBoundedFiniteBalancing
import «section 4».RVBoundedTensor

/-! The actual bounded measured product comparison and evaluation on the tensor
over the intrinsic finite-Gamma ring. No tensor injectivity, surjectivity
or global RV descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedBalancedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) :=
  RESChartRing.Ring B ⊗[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVPresentation.ChartRing B

def resComparison (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVBoundedRing.Ring B where
  toRingHom := RVBoundedMaps.ofRES B
  commutes' _ := rfl

def gammaComparison (B : Base (M := M)) :
    GammaBoundedRVPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVBoundedRing.Ring B where
  toRingHom := GammaBoundedRVMaps.sharp B
  commutes' c := (RingHom.congr_fun (GammaFiniteRVMaps.sharp_bounded_comparison B) c).symm

def comparison (B : Base (M := M)) : Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVBoundedRing.Ring B :=
  Algebra.TensorProduct.lift (resComparison B) (gammaComparison B) (fun _ _ => Commute.all _ _)

theorem comparison_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) = RVBoundedMaps.ofRES B x * GammaBoundedRVMaps.sharp B y := rfl

def resEvaluation (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B where
  toRingHom := RESOrdinaryReduction.forget B
  commutes' _ := rfl

def gammaEvaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaBoundedRVPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B where
  toRingHom := (GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom
  commutes' c := (RESAllBoundedFiniteBalancing.finite_balance_apply hc h00 linear hκ hs B hr hγ hΓ k c).symm

def evaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (resEvaluation B) (gammaEvaluation hc h00 linear hκ hs B hr hγ hΓ k) (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESOrdinaryReduction.forget B x * GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k y := rfl

def resInclusion (B : Base (M := M)) :
    RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] Source B := Algebra.TensorProduct.includeLeft

def gammaInclusion (B : Base (M := M)) :
    GammaBoundedRVPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] Source B := Algebra.TensorProduct.includeRight

-- Match RingHom.toIntAlgHom when comparing with the integer tensor.
instance (priority := 1100) sourceIntAlgebra (B : Base (M := M)) : Algebra ℤ (Source B) := Ring.toIntAlgebra (Source B)

instance sourceIntScalarTower (B : Base (M := M)) : IsScalarTower ℤ ℤ (Source B) where
  smul_assoc a b x := by
    change (a * b) • x = a • (b • x)
    exact mul_smul a b x

def fromInteger (B : Base (M := M)) : RVBoundedTensor.Source B →ₐ[ℤ] Source B :=
  Algebra.TensorProduct.lift (resInclusion B).toRingHom.toIntAlgHom (gammaInclusion B).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem fromInteger_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    fromInteger B (x ⊗ₜ[ℤ] y) = x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y := by
  change (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) * (1 ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem comparison_fromInteger (B : Base (M := M)) :
    (comparison B).toRingHom.toIntAlgHom.comp (fromInteger B) = RVBoundedTensor.comparison B := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change comparison B (fromInteger B (x ⊗ₜ[ℤ] y)) = RVBoundedTensor.comparison B (x ⊗ₜ[ℤ] y)
  rw [fromInteger_tmul, comparison_tmul, RVBoundedTensor.comparison_tmul]

theorem evaluation_fromInteger (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    (evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom.toIntAlgHom.comp (fromInteger B) =
      RVBoundedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change evaluation hc h00 linear hκ hs B hr hγ hΓ k (fromInteger B (x ⊗ₜ[ℤ] y)) =
    RVBoundedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[ℤ] y)
  rw [fromInteger_tmul, evaluation_tmul, RVBoundedTensor.evaluation_tmul]

theorem comparison_res (B : Base (M := M)) (x : RESChartRing.Ring B) :
    comparison B (resInclusion B x) = RVBoundedMaps.ofRES B x := by
  change comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [comparison_tmul, map_one, mul_one]

theorem evaluation_res (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (resInclusion B x) = RESOrdinaryReduction.forget B x := by
  change evaluation hc h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [evaluation_tmul, map_one, mul_one]

theorem evaluation_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k = evaluation hc h00 linear hκ hs B hr hγ hΓ l := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [evaluation_tmul, evaluation_tmul]
  exact congrArg (RESOrdinaryReduction.forget B x * ·)
    (RingHom.congr_fun (GammaBoundedRVProfiles.evaluation_independent_kind hc h00 linear hκ hs B hr hγ hΓ k l) y)

end DiamondIntegral.Section4.RVBoundedBalancedTensor
