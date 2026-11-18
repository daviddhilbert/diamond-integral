import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRelations
import «section 3».GammaGroundMapRelations

/-! Surjective descent of a Gamma-ground map to an arbitrary imaginary
target, with the full original-ground graph retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q R : Space LRV M}
variable {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q} {E : GammaGroundDefSet hc B R}

def gammaGroundSurjectiveDescent (f : GammaGroundMap A D) (hf : Function.Surjective f)
    (g : GammaGroundMap A E) (hg : ∀ a b, f a = f b → g a = g b) : GammaGroundMap D E where
  toFun d := g (hf d).choose
  graph_definable := by
    have h := f.relation_definable.symm.comp g.relation_definable
    change GammaGroundRelationDefinable hc B Q R
      (fun x y => ∃ d : D,d.val=x ∧ (g (hf d).choose).val=y)
    apply h.congr
    intro x y
    constructor
    · rintro ⟨z,⟨a,ha,hfa⟩,b,hb,hgb⟩
      have he : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      refine ⟨f a,hfa,?_⟩
      have hp := hg (hf (f a)).choose a (hf (f a)).choose_spec
      exact (congrArg Subtype.val hp).trans hgb
    · rintro ⟨d,hd,hgd⟩
      let a := (hf d).choose
      have ha : f a = d := (hf d).choose_spec
      exact ⟨a.val,⟨a,rfl,(congrArg Subtype.val ha).trans hd⟩,a,rfl,hgd⟩

@[simp] theorem gammaGroundSurjectiveDescent_apply
    (f : GammaGroundMap A D) (hf : Function.Surjective f)
    (g : GammaGroundMap A E) (hg : ∀ a b, f a = f b → g a = g b) (a : A) :
    gammaGroundSurjectiveDescent f hf g hg (f a) = g a :=
  hg (hf (f a)).choose a (hf (f a)).choose_spec

end DiamondIntegral.Section3
