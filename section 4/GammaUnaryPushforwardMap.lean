import «section 4».GammaWeightedPushforward
import «section 4».GammaDefinableConvolution
import «section 4».EulerFibreIntegral

/-! The actual additive unary pushforward on original-base definable
Euler functions. Its construction, additivity and integral preservation
come from the proved weighted fibre theorem and uniqueness. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryPushforwardMap
open GammaOrderLogic GammaDefinableEuler GammaDefinableConvolution EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def paperMap (T : Values.Gamma (M := M) → Values.Gamma (M := M)) :
    PaperGamma (M := M) → PaperGamma (M := M) :=
  fun x => toPaperGamma (T (toPaperGamma.symm x))

theorem exists_base_image (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | T (z 0) = z 1})
    (f : baseSubgroup B k) :
    ∃ P : baseSubgroup B k, IsUnaryImage k (paperMap T) f.val P.val ∧
      totalEuler k P.val = totalEuler k f.val := by
  obtain ⟨P, hdP, F, hF, hP, hEuler⟩ :=
    GammaWeightedPushforward.exists_weighted_image h00 linear B hΓ k f.val f.property T hT
  refine ⟨⟨P, hdP⟩, ?_, hEuler⟩
  intro y
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective y
  refine ⟨F (toPaperGamma γ), ?_, hP γ⟩
  intro x
  obtain ⟨δ, rfl⟩ := toPaperGamma.surjective x
  rw [hF]
  change (if T δ = γ then f.val (toPaperGamma δ) else 0) =
    if toPaperGamma (T δ) = toPaperGamma γ then f.val (toPaperGamma δ) else 0
  by_cases h : T δ = γ
  · simp only [h, ite_true]
  · have hn : toPaperGamma (T δ) ≠ toPaperGamma γ := fun he => h (toPaperGamma.injective he)
    simp only [h, hn, ite_false]

def pushforward (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | T (z 0) = z 1}) :
    baseSubgroup B k →+ baseSubgroup B k where
  toFun f := Classical.choose (exists_base_image h00 linear B hΓ k T hT f)
  map_zero' := by
    apply Subtype.ext
    exact (Classical.choose_spec (exists_base_image h00 linear B hΓ k T hT 0)).1.unique
      (isUnaryImage_zero k (paperMap T))
  map_add' f g := by
    apply Subtype.ext
    exact (Classical.choose_spec (exists_base_image h00 linear B hΓ k T hT (f + g))).1.unique
      ((Classical.choose_spec (exists_base_image h00 linear B hΓ k T hT f)).1.add
        (Classical.choose_spec (exists_base_image h00 linear B hΓ k T hT g)).1)

theorem pushforward_spec (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | T (z 0) = z 1})
    (f : baseSubgroup B k) :
    IsUnaryImage k (paperMap T) f.val (pushforward h00 linear B hΓ k T hT f).val ∧
      totalEuler k (pushforward h00 linear B hΓ k T hT f).val = totalEuler k f.val :=
  Classical.choose_spec (exists_base_image h00 linear B hΓ k T hT f)

theorem pushforward_id (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 = z 1})
    (f : baseSubgroup B k) : pushforward h00 linear B hΓ k id hT f = f := by
  apply Subtype.ext
  have h := (pushforward_spec h00 linear B hΓ k id hT f).1
  have he : paperMap (id : Values.Gamma (M := M) → Values.Gamma (M := M)) = id := by
    funext x
    exact toPaperGamma.apply_symm_apply x
  rw [he] at h
  exact h.unique (isUnaryImage_id k f.val)

end DiamondIntegral.Section4.GammaUnaryPushforwardMap
