import «section 3».GammaGroundMapRestrictions

/-! Two actual original-ground map graphs glue along a definable
predicate, with their complete point functions retained. -/
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
variable {Q R : Space LRV M} {A : GammaGroundDefSet hc B Q} {E : GammaGroundDefSet hc B R}

def GammaGroundMap.binaryPieces (f g : GammaGroundMap A E) (D : GammaGroundDefSet hc B Q) : GammaGroundMap A E where
  toFun p := if p.val ∈ D.carrier then f p else g p
  graph_definable := by
    have hD : GammaGroundDefinable hc B (Q.prod R) {z | z.1 ∈ D.carrier} :=
      D.definable.preimage (universalProductFst Q R B.real)
    apply ((f.graph_definable.inter hD).union (g.graph_definable.inter hD.compl)).congr
    intro z
    constructor
    · rintro (⟨⟨p,hp,hf⟩,hd⟩ | ⟨⟨p,hp,hg⟩,hd⟩)
      · have hmem : p.val ∈ D.carrier := hp.symm ▸ hd
        exact ⟨p,hp,by simpa only [ite_eq_left hmem] using hf⟩
      · have hmem : p.val ∉ D.carrier := hp.symm ▸ hd
        exact ⟨p,hp,by simpa only [ite_eq_right hmem] using hg⟩
    · rintro ⟨p,hp,h⟩
      by_cases hd : p.val ∈ D.carrier
      · refine Or.inl ⟨⟨p,hp,by simpa only [ite_eq_left hd] using h⟩,?_⟩
        change z.1 ∈ D.carrier
        exact hp ▸ hd
      · refine Or.inr ⟨⟨p,hp,by simpa only [ite_eq_right hd] using h⟩,?_⟩
        change z.1 ∉ D.carrier
        exact hp ▸ hd

theorem GammaGroundMap.binaryPieces_apply (f g : GammaGroundMap A E) (D : GammaGroundDefSet hc B Q) (p : A) :
    f.binaryPieces g D p = if p.val ∈ D.carrier then f p else g p := rfl

end DiamondIntegral.Section3
