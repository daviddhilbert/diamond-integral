import «section 3».GammaGroundMaps
import «section 3».NamedMapComposition

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {ground : GammaParameters.Base (M := M)}

def GammaGroundMap.comp {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}
    (g : GammaGroundMap B D) (f : GammaGroundMap A B) : GammaGroundMap A D where
  toFun a := g (f a)
  graph_definable := by
    let H : Set (Q.prod (R.prod T)).Carrier := {z |
      (∃ a : A, a.val = z.1 ∧ (f a).val = z.2.1) ∧
      (∃ b : B, b.val = z.2.1 ∧ (g b).val = z.2.2)}
    have hH : GammaGroundDefinable hc ground (Q.prod (R.prod T)) H :=
      (f.graph_definable.preimage (universalTripleFirstSecond Q R T ground.real)).inter
        (g.graph_definable.preimage (universalProductSnd Q (R.prod T) ground.real))
    apply (hH.image (universalTripleFirstThird Q R T ground.real)).congr
    intro z
    constructor
    · rintro ⟨w, ⟨⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩, hw⟩
      have hfb : f a = b := Subtype.ext (hfa.trans hb.symm)
      refine ⟨a, ha.trans (congrArg Prod.fst hw), ?_⟩
      exact (congrArg (fun b : B => (g b).val) hfb).trans (hgb.trans (congrArg Prod.snd hw))
    · rintro ⟨a, ha, hga⟩
      exact ⟨(a.val, ((f a).val, (g (f a)).val)),
        ⟨⟨a, rfl, rfl⟩, ⟨f a, rfl, rfl⟩⟩, Prod.ext ha hga⟩

@[simp] theorem GammaGroundMap.comp_apply {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}
    (g : GammaGroundMap B D) (f : GammaGroundMap A B) (a : A) : (g.comp f) a = g (f a) := rfl


end DiamondIntegral.Section3
