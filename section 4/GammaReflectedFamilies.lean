import «section 4».GammaHigherProjection
import «section 4».GammaDefinableMaps
import «section 4».EulerReflection

/-! Actual reflection of unary original-base integer families around a
named Gamma value, with its Euler-function evaluation identified. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaReflectedFamilies
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaIntegerFamilies GammaHigherProjection
open GammaUnaryFamilyBridge EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def reflectionMap (a : Values.Gamma (M := M)) (z : Fin 1 → Values.Gamma (M := M)) :
    Values.Gamma (M := M) := a * (z 0)⁻¹

theorem reflectionMap_definable (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) : MapDefinable B (reflectionMap a) :=
  mul_definable B _ _ (constant_definable B a ha) (inverse_definable B _ (projection_definable B 0))

theorem reflectionMap_graph (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) :
    GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 = reflectionMap a (Fin.tail z)} := by
  have h := reflectionMap_definable B a ha
  unfold MapDefinable at h
  convert h using 1
  ext z
  rfl

def reflectFamily (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) (f : familySubgroup B 1) : familySubgroup B 1 :=
  unaryCompose B (reflectionMap a) (reflectionMap_graph B a ha) f

theorem reflectFamily_eval (B : Base (M := M)) (a : Values.Gamma (M := M))
    (ha : GammaDefinableClosureAtBase B a) (f : familySubgroup B 1) (γ : Values.Gamma (M := M)) :
    (reflectFamily B a ha f).val ![γ] = f.val ![a * γ⁻¹] := rfl

theorem reflectFamily_toEuler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (a : Values.Gamma (M := M)) (ha : GammaDefinableClosureAtBase B a) (f : familySubgroup B 1) :
    (toEuler h00 B k (reflectFamily B a ha f)).val = reflectAt k (toPaperGamma a) (toEuler h00 B k f).val := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change (toEuler h00 B k (reflectFamily B a ha f)).val (toPaperGamma γ) =
    reflectAt k (toPaperGamma a) (toEuler h00 B k f).val (toPaperGamma γ)
  rw [toEuler_eval, reflectFamily_eval, reflectAt_eval]
  have he : toPaperGamma a - toPaperGamma γ = toPaperGamma (a * γ⁻¹) := rfl
  rw [he, toEuler_eval]

theorem toEuler_extend (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (C : Set (Values.Gamma (M := M))) (k : EulerKind) (f : familySubgroup B 1) :
    (toEuler h00 (GammaBaseExtension.withGamma B C) k (GammaProductFamilies.extendFamily B C f)).val =
      (toEuler h00 B k f).val := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change (toEuler h00 (GammaBaseExtension.withGamma B C) k (GammaProductFamilies.extendFamily B C f)).val
      (toPaperGamma γ) = (toEuler h00 B k f).val (toPaperGamma γ)
  rw [toEuler_eval, toEuler_eval]
  rfl

end DiamondIntegral.Section4.GammaReflectedFamilies
