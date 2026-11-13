import «section 3».GammaGroundFiniteProducts

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q R T : Space LRV M}
variable {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
variable {D : GammaGroundDefSet hc ground R} {E : GammaGroundDefSet hc ground T}

def GammaGroundBijection.prodMap (f : GammaGroundBijection A D) (g : GammaGroundBijection B E) :
    GammaGroundBijection (A.prod B) (D.prod E) where
  map := f.map.prodMap g.map
  bijective := by
    constructor
    · intro a b hab
      have he := congrArg (fun z : D.prod E => z.val) hab
      have ha := f.bijective.injective (Subtype.ext (congrArg Prod.fst he))
      have hb := g.bijective.injective (Subtype.ext (congrArg Prod.snd he))
      exact Subtype.ext (Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb))
    · intro z
      obtain ⟨a, ha⟩ := f.bijective.surjective ⟨z.val.1, z.property.1⟩
      obtain ⟨b, hb⟩ := g.bijective.surjective ⟨z.val.2, z.property.2⟩
      exact ⟨⟨(a.val, b.val), a.property, b.property⟩,
        Subtype.ext (Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb))⟩

end DiamondIntegral.Section3
