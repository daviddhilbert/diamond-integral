import «section 4».GammaIteratedIntegral
import «section 4».GammaDefinableConvolution

/-! Unary integer families are the existing original-base Euler functions.
The bridge is additive and preserves actual evaluation and integration. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryFamilyBridge
open GammaDefinableEuler GammaDefinableFunctions GammaDefinableConvolution GammaOrderLogic
open GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unary_definable (B : Base (M := M)) (f : familySubgroup B 1) :
    IntegerDefinable B (fun γ => f.val ![γ]) := by
  have hf : IntegerFamilyDefinable B f.val := f.property
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro a ⟨γ, rfl⟩
    exact ⟨![γ], rfl⟩
  · intro a
    apply (unary_definable_iff B _).mp
    convert hf.2 a using 1
    ext z
    have he : ![z 0] = z := by
      funext i
      fin_cases i
      rfl
    change f.val ![z 0] = a ↔ f.val z = a
    rw [he]

def toEuler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) :
    familySubgroup B 1 →+ baseSubgroup B k where
  toFun f := ⟨unaryFunction h00 B k f.val f.property, by
    change IntegerDefinable B _
    have he : (fun γ => unaryFunction h00 B k f.val f.property (toPaperGamma γ)) =
        (fun γ => f.val ![γ]) := funext (unaryFunction_eval h00 B k f.val f.property)
    rw [he]
    exact unary_definable B f⟩
  map_zero' := by
    apply Subtype.ext
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    have h0 : IntegerFamilyDefinable B (0 : familySubgroup B 1).val := (0 : familySubgroup B 1).property
    change unaryFunction h00 B k (0 : familySubgroup B 1).val h0
      (toPaperGamma γ) = (0 : EulerFunction k (PaperGamma (M := M))) (toPaperGamma γ)
    rw [unaryFunction_eval, eval_zero]
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    have hf : IntegerFamilyDefinable B f.val := f.property
    have hg : IntegerFamilyDefinable B g.val := g.property
    have hsum : IntegerFamilyDefinable B (f + g).val := (f + g).property
    change unaryFunction h00 B k (f + g).val hsum (toPaperGamma γ) =
      (unaryFunction h00 B k f.val hf + unaryFunction h00 B k g.val hg) (toPaperGamma γ)
    rw [unaryFunction_eval, eval_add, unaryFunction_eval, unaryFunction_eval]
    rfl

theorem toEuler_eval (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (f : familySubgroup B 1) (γ : Values.Gamma (M := M)) :
    (toEuler h00 B k f).val (toPaperGamma γ) = f.val ![γ] :=
  unaryFunction_eval h00 B k f.val f.property γ

theorem toEuler_integral (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (f : familySubgroup B 1) :
    totalEuler k (toEuler h00 B k f).val = integrateAll h00 hκ hs B hr hγ k 1 f := rfl

end DiamondIntegral.Section4.GammaUnaryFamilyBridge
