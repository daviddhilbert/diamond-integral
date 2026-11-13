import «section 4».RVOrdinaryBalancedGradings
import «section 4».RVOrdinaryTensorEvaluation
import «section 4».RESOrdinarySurjectivity

/-! Forgetting volume induces a surjective map from the measured balanced
tensor to the actual ordinary balanced tensor. The coefficient base also
changes to the ordinary finite Gamma ring. Both RV comparison and both
ordinary Euler evaluations commute on the whole tensor. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryTensorForget
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forget (B : Base (M := M)) : RVFiniteBalancedTensor.Source B →+* RVOrdinaryBalancedTensor.Source B :=
  Algebra.TensorProduct.mapRingHom (GammaOrdinaryFiniteRing.forget B)
    (RESOrdinaryRing.forget B) (GammaOrdinaryRing.forget B)
    (GammaOrdinaryFiniteMaps.sharp_forget_square B).symm
    (GammaOrdinaryFiniteMaps.full_forget_square B).symm

theorem forget_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    forget B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESOrdinaryRing.forget B x ⊗ₜ[GammaOrdinaryAlgebras.Coeff B] GammaOrdinaryRing.forget B y :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ x y

theorem forget_surjective (B : Base (M := M)) : Function.Surjective (forget B) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨a, rfl⟩ := RESOrdinarySurjectivity.forget_surjective B x
    obtain ⟨b, rfl⟩ := GammaOrdinaryRing.forget_surjective B y
    exact ⟨a ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] b, forget_tmul B a b⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

theorem comparison_square (B : Base (M := M)) :
    (RVOrdinaryBalancedTensor.comparison B).toRingHom.comp (forget B) =
      (RVOrdinaryRing.forget B).comp (RVFiniteBalancedTensor.comparison B).toRingHom := by
  apply DFunLike.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change RVOrdinaryBalancedTensor.comparison B (forget B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) = _
    rw [forget_tmul, RVOrdinaryBalancedTensor.comparison_tmul]
    change _ = RVOrdinaryRing.forget B (RVFiniteBalancedTensor.comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y))
    rw [RVFiniteBalancedTensor.comparison_tmul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun (RVOrdinaryMaps.forget_ofRES B) x).symm
      (RingHom.congr_fun (GammaOrdinarySharpRingMap.forget_square B) y)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

def gradedForget (B : Base (M := M)) :
    GradedRingHom (RVBalancedGradings.measuredPiece B) (RVOrdinaryBalancedGradings.piece B) :=
  TensorGradedMaps.gradedMap (RVBalancedGradings.measuredData B) (RVOrdinaryBalancedGradings.coaction B) (forget B) (by
    intro m n x y hx hy
    change forget B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RVOrdinaryBalancedGradings.piece B (m + n)
    rw [forget_tmul]
    exact RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.forget_mem B hx) (GammaOrdinaryGrading.forget_mem B hy))

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_square (k : EulerKind) :
    (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.comp (forget B) =
      (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  apply DFunLike.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k
      (forget B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) = _
    rw [forget_tmul, RVOrdinaryBalancedTensor.evaluation_tmul]
    change _ = RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)
    rw [RVOrdinaryTensorEvaluation.evaluation_tmul]
    exact congrArg (RESOrdinaryReduction.forget B x * ·)
      (RingHom.congr_fun (GammaOrdinaryRESEvaluation.evaluation_forget h00 linear hκ hs B hr hγ hΓ k) y)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end DiamondIntegral.Section4.RVOrdinaryTensorForget
