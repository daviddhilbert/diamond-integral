import «section 3».GammaGroundMapRestrictions

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

def GammaGroundMap.pair {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}
    (f : GammaGroundMap A B) (g : GammaGroundMap A D) : GammaGroundMap A (B.prod D) where
  toFun a := ⟨((f a).val, (g a).val), (f a).property, (g a).property⟩
  graph_definable := by
    have hF := f.graph_definable.preimage (universalTripleFirstSecond Q R T ground.real)
    have hG := g.graph_definable.preimage (universalTripleFirstThird Q R T ground.real)
    apply (hF.inter hG).congr
    intro z
    constructor
    · rintro ⟨⟨a, ha, hf⟩, ⟨b, hb, hg⟩⟩
      have he : b = a := Subtype.ext (hb.trans ha.symm)
      subst b
      exact ⟨a, ha, Prod.ext hf hg⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, ha, congrArg Prod.fst he⟩, ⟨a, ha, congrArg Prod.snd he⟩⟩

def GammaGroundMap.prodMap {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    {D : GammaGroundDefSet hc ground T} {E : GammaGroundDefSet hc ground U}
    (f : GammaGroundMap A D) (g : GammaGroundMap B E) : GammaGroundMap (A.prod B) (D.prod E) :=
  (f.comp (GammaGroundMap.prodFst A B)).pair (g.comp (GammaGroundMap.prodSnd A B))


end DiamondIntegral.Section3
