import «section 4».GammaBoundedFunctions

/-! Both unary Euler theories give the same bounded function ring and
Euler functional, preserving the original definability base. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section4.GammaBoundedComparison
open GammaDefinableEuler GammaDefinableFunctions GammaBoundedFunctions EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def changeBaseKind (B : GammaParameters.Base (M := M)) (k l : EulerKind) :
    boundedBaseSubring B k ≃+* boundedBaseSubring B l where
  toFun f := ⟨changeKind k l f.val, by
    constructor
    · change IntegerDefinable B (fun γ => changeKind k l f.val (toPaperGamma γ))
      have hf : IntegerDefinable B (fun γ => f.val (toPaperGamma γ)) := f.property.1
      simpa only [changeKind_eval] using hf
    · exact f.property.2.changeKind l⟩
  invFun f := ⟨changeKind l k f.val, by
    constructor
    · change IntegerDefinable B (fun γ => changeKind l k f.val (toPaperGamma γ))
      have hf : IntegerDefinable B (fun γ => f.val (toPaperGamma γ)) := f.property.1
      simpa only [changeKind_eval] using hf
    · exact f.property.2.changeKind k⟩
  left_inv f := by
    apply Subtype.ext
    change changeKind l k (changeKind k l f.val) = f.val
    rw [changeKind_trans, changeKind_self]
  right_inv f := by
    apply Subtype.ext
    change changeKind k l (changeKind l k f.val) = f.val
    rw [changeKind_trans, changeKind_self]
  map_mul' f g := Subtype.ext (changeKind_mul_of_bounded k l f.val g.val f.property.2)
  map_add' f g := Subtype.ext ((changeKind k l).map_add f.val g.val)

theorem changeBaseKind_eval (B : GammaParameters.Base (M := M)) (k l : EulerKind)
    (f : boundedBaseSubring B k) (x : PaperGamma (M := M)) :
    (changeBaseKind B k l f).val x = f.val x := changeKind_eval k l f.val x

theorem baseBoundedEuler_changeKind (B : GammaParameters.Base (M := M)) (k l : EulerKind)
    (f : boundedBaseSubring B k) :
    baseBoundedEuler B l (changeBaseKind B k l f) = baseBoundedEuler B k f :=
  totalEuler_changeKind k l f.val f.property.2

end DiamondIntegral.Section4.GammaBoundedComparison
