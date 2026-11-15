import «section 3».GammaGroundBijections
import «section 3».GammaGroundMapUnions
import «section 3».GammaGroundRVTags

/-! Actual same-base definable bijections assemble on disjoint unions,
including the literal RV zero/one tagged coproducts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

def gammaGroundDisjointUnionBijection
    {A C : GammaGroundDefSet hc B Q} {D E : GammaGroundDefSet hc B R}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection C E)
    (hAC : Disjoint A.carrier C.carrier) (hDE : Disjoint D.carrier E.carrier) :
    GammaGroundBijection (A.union C) (D.union E) := by
  let F : GammaGroundMap A (D.union E) := f.map.corestrict (fun x => Or.inl (f.map x).property)
  let H : GammaGroundMap C (D.union E) := g.map.corestrict (fun x => Or.inr (g.map x).property)
  let u := F.union H
  have hleft (x : A) : u ⟨x.val, Or.inl x.property⟩ = F x := GammaGroundMap.union_on_left F H x
  have hright (x : C) : u ⟨x.val, Or.inr x.property⟩ = H x := GammaGroundMap.union_on_right F H hAC x
  refine ⟨u, ?_, ?_⟩
  · intro x y he
    rcases x.property with hx | hx
    · rcases y.property with hy | hy
      · have hh : F ⟨x.val, hx⟩ = F ⟨y.val, hy⟩ :=
          (hleft ⟨x.val, hx⟩).symm.trans (he.trans (hleft ⟨y.val, hy⟩))
        have hv : (f.map ⟨x.val, hx⟩).val = (f.map ⟨y.val, hy⟩).val :=
          congrArg (fun z : D.union E => z.val) hh
        have hxy := f.bijective.injective (Subtype.ext hv)
        exact Subtype.ext (congrArg (fun z : A => z.val) hxy)
      · have hh : F ⟨x.val, hx⟩ = H ⟨y.val, hy⟩ :=
          (hleft ⟨x.val, hx⟩).symm.trans (he.trans (hright ⟨y.val, hy⟩))
        exact False.elim (Set.disjoint_left.mp hDE (f.map ⟨x.val, hx⟩).property
          ((congrArg Subtype.val hh).symm ▸ (g.map ⟨y.val, hy⟩).property))
    · rcases y.property with hy | hy
      · have hh : H ⟨x.val, hx⟩ = F ⟨y.val, hy⟩ :=
          (hright ⟨x.val, hx⟩).symm.trans (he.trans (hleft ⟨y.val, hy⟩))
        exact False.elim (Set.disjoint_left.mp hDE
          ((congrArg Subtype.val hh).symm ▸ (f.map ⟨y.val, hy⟩).property) (g.map ⟨x.val, hx⟩).property)
      · have hh : H ⟨x.val, hx⟩ = H ⟨y.val, hy⟩ :=
          (hright ⟨x.val, hx⟩).symm.trans (he.trans (hright ⟨y.val, hy⟩))
        have hv : (g.map ⟨x.val, hx⟩).val = (g.map ⟨y.val, hy⟩).val :=
          congrArg (fun z : D.union E => z.val) hh
        have hxy := g.bijective.injective (Subtype.ext hv)
        exact Subtype.ext (congrArg (fun z : C => z.val) hxy)
  · intro y
    rcases y.property with hy | hy
    · obtain ⟨x, hx⟩ := f.bijective.surjective ⟨y.val, hy⟩
      refine ⟨⟨x.val, Or.inl x.property⟩, (hleft x).trans ?_⟩
      exact Subtype.ext (congrArg (fun z : D => z.val) hx)
    · obtain ⟨x, hx⟩ := g.bijective.surjective ⟨y.val, hy⟩
      refine ⟨⟨x.val, Or.inr x.property⟩, (hright x).trans ?_⟩
      exact Subtype.ext (congrArg (fun z : E => z.val) hx)

def gammaGroundRVTaggedUnion {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) :
    GammaGroundDefSet hc B (rawRVSpace (M := M) (1 + (n + m))) :=
  (gammaGroundRVLeftTag A m).image.union (gammaGroundRVRightTag C n).image

def gammaGroundRVLeftTagBijection {n : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) (m : ℕ) :
    GammaGroundBijection A (gammaGroundRVLeftTag A m).image :=
  ⟨(gammaGroundRVLeftTag A m).toImage,
    (gammaGroundRVLeftTag A m).toImage_bijective (gammaGroundRVLeftTag_injective A m)⟩

def gammaGroundRVRightTagBijection {m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (n : ℕ) :
    GammaGroundBijection A (gammaGroundRVRightTag A n).image :=
  ⟨(gammaGroundRVRightTag A n).toImage,
    (gammaGroundRVRightTag A n).toImage_bijective (gammaGroundRVRightTag_injective A n)⟩

def gammaGroundRVTaggedUnionBijection {n m p q : ℕ}
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    {C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)}
    {D : GammaGroundDefSet hc B (rawRVSpace (M := M) p)}
    {E : GammaGroundDefSet hc B (rawRVSpace (M := M) q)}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection C E) :
    GammaGroundBijection (gammaGroundRVTaggedUnion A C) (gammaGroundRVTaggedUnion D E) :=
  gammaGroundDisjointUnionBijection
    ((gammaGroundRVLeftTagBijection D q).comp (f.comp (gammaGroundRVLeftTagBijection A m).symm))
    ((gammaGroundRVRightTagBijection E p).comp (g.comp (gammaGroundRVRightTagBijection C n).symm))
    (gammaGroundRVTaggedImages_disjoint A C) (gammaGroundRVTaggedImages_disjoint D E)

end DiamondIntegral.Section5
