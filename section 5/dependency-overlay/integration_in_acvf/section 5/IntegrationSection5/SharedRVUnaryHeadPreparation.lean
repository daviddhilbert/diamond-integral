import IntegrationSection5.SharedRVProductImage
import IntegrationSection5.UnaryProductHeadPreparation

/-! Uniform product-head preparation with shared RV coordinates. Exact lifted images construct head saturation, and all old-label projections are computed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n a b l : ℕ}

theorem sharedRV_unary_product_head_preparation
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B))
    (H : DefSet (M := M) S (n+1) l) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin a → Fin l)
    (Q : Point (M := M) (n+1) l → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hSource : carrier H = {p | activeUnaryProjection 0 ρ p ∈ carrier A ∧ Q p}) :
    ∃ T : HeadPreparation H, ∃ σ : Fin b → Fin T.arity, ∃ hle : l ≤ T.arity,
      GammaSetDefinable G (carrier T.target) ∧ GammaGraphDefinable G (pointMapGraph T.map) ∧
      (Function.Bijective ρ → Function.Bijective σ) ∧
      (∀ j : Fin a, σ (suffixIndex (special_chain_rvArity_le u.chain) j) = suffixIndex hle (ρ j)) ∧
      (∀ j : Fin T.arity, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) ∧
      carrier T.target = {q | activeUnaryProjection 0 σ q ∈ carrier B ∧ Q (retainedPoint hle q)} ∧
      ∀ p : H, activeUnaryProjection 0 σ (T.map p).val =
        (u.toMap ⟨activeUnaryProjection 0 ρ p.val,
          ((Set.ext_iff.mp hSource p.val).mp p.property).1⟩).val := by
  have hHA : ∀ p ∈ carrier H, activeUnaryProjection 0 ρ p ∈ carrier A :=
    fun p hp => ((Set.ext_iff.mp hSource p).mp hp).1
  obtain ⟨r,K,σ,hle,f,hf,hσ,hK,hfG,hcompat,hcover,hcomm⟩ :=
    gamma_unary_coordinateLift u.chain hu H hH 0 ρ hHA none u.alternating
  have hImage := coordinate_lift_product_image_sharedRV u f 0
    (specialRelativeBoundary_forget hf) hle ρ σ Q hQ hSource hcomm hcompat hcover
  let T : HeadPreparation H := ⟨r,K,f,specialRelativeBoundary_forget hf,
    unary_product_head_saturated hB σ hle Q hQ hImage⟩
  exact ⟨T,σ,hle,hK,hfG,hσ,hcompat,hcover,hImage,hcomm⟩

end IntegrationInACVF.Section5
