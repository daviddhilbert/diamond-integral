import «section 4».GammaHigherPushforward
import «section 4».GammaProductFamilies

/-! Pushforward along an actual constant Gamma map is the source integral
times the point mass. This computes counterweighted objects directly. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaConstantPushforward
open GammaDefinableEuler GammaOrderLogic GammaIntegerFamilies GammaHigherPushforward GammaProductFamilies
open GammaIntegralCongruence GammaParameterExtension GammaIteratedIntegral GammaBaseExtension EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pushforward_constant (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (c : Values.Gamma (M := M)) (hconst : ∀ z, T z = c) (f : familySubgroup B n) :
    (pushforward h00 hκ hs B hr hγ k T hT f).val =
      (integrateAll h00 hκ hs B hr hγ k n f) • point k (toPaperGamma c) := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (pushforward h00 hκ hs B hr hγ k T hT f).val (toPaperGamma a) =
    ((integrateAll h00 hκ hs B hr hγ k n f) • point k (toPaperGamma c)) (toPaperGamma a)
  rw [pushforward_eval, eval_zsmul, point_eval]
  let C := withGamma B (Set.range ![a])
  have hγC : Cardinal.mk C.gamma < κ := finite_gamma_extension_small hκ B hγ ![a]
  let F := fibreFamily B T hT f a
  by_cases hca : c = a
  · have he : F = extendFamily B (Set.range ![a]) f := by
      apply Subtype.ext
      funext u
      change (fibreFamily B T hT f a).val u = f.val u
      rw [fibreFamily_eval, hconst u, hca, ite_eq_left rfl]
    have hi := integrateAll_congr h00 hκ hs C B hr hγC hr hγ k n F f (by
      intro u
      exact congrArg (fun q => q.val u) he)
    have hpaper : toPaperGamma a = toPaperGamma c := congrArg toPaperGamma hca.symm
    rw [ite_eq_left hpaper]
    simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using hi
  · have he : F = 0 := by
      apply Subtype.ext
      funext u
      change (fibreFamily B T hT f a).val u = 0
      rw [fibreFamily_eval, hconst u, ite_eq_right hca]
    have hpaper : toPaperGamma a ≠ toPaperGamma c := fun h => hca (toPaperGamma.injective h).symm
    rw [ite_eq_right hpaper]
    change integrateAll h00 hκ hs C hr hγC k n F = _
    rw [he, map_zero, zsmul_zero]

end DiamondIntegral.Section4.GammaConstantPushforward
