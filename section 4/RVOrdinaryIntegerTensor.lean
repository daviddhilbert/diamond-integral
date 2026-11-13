import «section 4».RVOrdinaryBalancedTensor

/-! The ordinary component maps are first defined over the integers.
Their actual finite-Gamma-balanced tensor quotient map is surjective,
and the whole comparison and Euler maps commute with that quotient. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryIntegerTensor
open GammaOrdinaryAlgebras RVOrdinaryBalancedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance (priority := 1100) sourceIntAlgebra (B : Base (M := M)) : Algebra ℤ (Source B) := Ring.toIntAlgebra (Source B)
instance sourceIntScalarTower (B : Base (M := M)) : IsScalarTower ℤ ℤ (Source B) where
  smul_assoc a b x := by
    change (a * b) • x = a • (b • x)
    exact mul_smul a b x

def resInclusion (B : Base (M := M)) : RESOrdinaryRing.Ring B →ₐ[Coeff B] Source B := Algebra.TensorProduct.includeLeft

def gammaInclusion (B : Base (M := M)) : GammaOrdinaryRing.Ring B →ₐ[Coeff B] Source B := Algebra.TensorProduct.includeRight

def fromInteger (B : Base (M := M)) : IntegerSource B →ₐ[ℤ] Source B :=
  Algebra.TensorProduct.lift (resInclusion B).toRingHom.toIntAlgHom (gammaInclusion B).toRingHom.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem fromInteger_tmul (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) (y : GammaOrdinaryRing.Ring B) :
    fromInteger B (x ⊗ₜ[ℤ] y) = x ⊗ₜ[Coeff B] y := by
  change (x ⊗ₜ[Coeff B] 1) * (1 ⊗ₜ[Coeff B] y) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem fromInteger_surjective (B : Base (M := M)) : Function.Surjective (fromInteger B) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ⟨x ⊗ₜ[ℤ] y, fromInteger_tmul B x y⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

def integerComparison (B : Base (M := M)) : IntegerSource B →ₐ[ℤ] RVOrdinaryRing.Ring B :=
  Algebra.TensorProduct.lift (RVOrdinaryMaps.ofRES B).toIntAlgHom (GammaOrdinarySharpRingMap.sharp B).toIntAlgHom (fun _ _ => Commute.all _ _)

theorem comparison_fromInteger (B : Base (M := M)) :
    (comparison B).toRingHom.toIntAlgHom.comp (fromInteger B) = integerComparison B := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change comparison B (fromInteger B (x ⊗ₜ[ℤ] y)) = _
  rw [fromInteger_tmul, comparison_tmul]
  rfl

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def integerEvaluation (k : EulerKind) : IntegerSource B →ₐ[ℤ] RESOrdinaryReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (RESOrdinaryReduction.quotient B).toIntAlgHom
    (GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toIntAlgHom (fun _ _ => Commute.all _ _)

theorem evaluation_fromInteger (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.toIntAlgHom.comp (fromInteger B) = integerEvaluation h00 linear hκ hs B hr hγ hΓ k := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change evaluation h00 linear hκ hs B hr hγ hΓ k (fromInteger B (x ⊗ₜ[ℤ] y)) = _
  rw [fromInteger_tmul, evaluation_tmul]
  rfl

end DiamondIntegral.Section4.RVOrdinaryIntegerTensor
