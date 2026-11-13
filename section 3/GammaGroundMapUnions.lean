import «section 3».GammaGroundFiniteProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M} {A B : GammaGroundDefSet hc ground Q} {D : GammaGroundDefSet hc ground R}

def GammaGroundMap.union (f : GammaGroundMap A D) (g : GammaGroundMap B D) :
    GammaGroundMap (A.union B) D where
  toFun a := if h : a.val ∈ A.carrier then f ⟨a.val, h⟩ else g ⟨a.val, a.property.resolve_left h⟩
  graph_definable := by
    classical
    have hB := g.graph_definable.inter (A.definable.preimage (universalProductFst Q R ground.real)).compl
    apply (f.graph_definable.union hB).congr
    intro z
    constructor
    · rintro (⟨a, ha, hf⟩ | ⟨⟨b, hb, hg⟩, hn⟩)
      · refine ⟨⟨a.val, Or.inl a.property⟩, ha, ?_⟩
        simpa only [dite_eq_left a.property] using hf
      · have hn' : b.val ∉ A.carrier := by
          intro h
          apply hn
          change z.1 ∈ A.carrier
          exact hb ▸ h
        refine ⟨⟨b.val, Or.inr b.property⟩, hb, ?_⟩
        simpa only [dite_eq_right hn'] using hg
    · rintro ⟨a, ha, hv⟩
      by_cases hm : a.val ∈ A.carrier
      · left
        exact ⟨⟨a.val, hm⟩, ha, by simpa only [dite_eq_left hm] using hv⟩
      · right
        exact ⟨⟨⟨a.val, a.property.resolve_left hm⟩, ha, by simpa only [dite_eq_right hm] using hv⟩,
          by
            intro h
            apply hm
            change z.1 ∈ A.carrier at h
            exact ha.symm ▸ h⟩

theorem GammaGroundMap.union_on_left (f : GammaGroundMap A D) (g : GammaGroundMap B D) (a : A) :
    f.union g ⟨a.val, Or.inl a.property⟩ = f a := dite_eq_left a.property

theorem GammaGroundMap.union_on_right (f : GammaGroundMap A D) (g : GammaGroundMap B D)
    (hd : Disjoint A.carrier B.carrier) (b : B) :
    f.union g ⟨b.val, Or.inr b.property⟩ = g b :=
  dite_eq_right (fun h => Set.disjoint_left.mp hd h b.property)

theorem GammaGroundMap.FiniteFibres.union {f : GammaGroundMap A D} {g : GammaGroundMap B D}
    (hf : f.FiniteFibres) (hg : g.FiniteFibres) : (f.union g).FiniteFibres := by
  classical
  intro t
  let il : A → A.union B := fun a => ⟨a.val, Or.inl a.property⟩
  let ir : B → A.union B := fun b => ⟨b.val, Or.inr b.property⟩
  apply (((hf t).image il).union ((hg t).image ir)).subset
  intro a ha
  by_cases hm : a.val ∈ A.carrier
  · exact Or.inl ⟨⟨a.val, hm⟩, by simpa only [Set.mem_setOf_eq, GammaGroundMap.union, dite_eq_left hm] using ha, rfl⟩
  · exact Or.inr ⟨⟨a.val, a.property.resolve_left hm⟩, by simpa only [Set.mem_setOf_eq, GammaGroundMap.union, dite_eq_right hm] using ha, rfl⟩

end DiamondIntegral.Section3
