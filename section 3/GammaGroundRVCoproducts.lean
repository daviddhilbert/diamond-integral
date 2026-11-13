import «section 3».GammaGroundRVTags
import «section 3».GammaGroundRVScissors
import Section4.PositiveAdditiveRepresentatives

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {k : ℕ}


def GammaGroundRVObject.coprod (U V : GammaGroundRVObject hc ground k) : GammaGroundRVObject hc ground k where
  arity := 1 + (U.arity + V.arity)
  domain := (gammaGroundRVLeftTag U.domain V.arity).image.union (gammaGroundRVRightTag V.domain U.arity).image
  volume := (U.volume.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (V.volume.comp (gammaGroundRVUntagRight V.domain U.arity))
  finite := (U.finite.comp (GammaGroundMap.finiteFibres_of_injective
    (Equiv.ofBijective (gammaGroundRVLeftTag U.domain V.arity).toImage
      ((gammaGroundRVLeftTag U.domain V.arity).toImage_bijective
        (gammaGroundRVLeftTag_injective U.domain V.arity))).symm.injective)).union
    (V.finite.comp (GammaGroundMap.finiteFibres_of_injective
      (Equiv.ofBijective (gammaGroundRVRightTag V.domain U.arity).toImage
        ((gammaGroundRVRightTag V.domain U.arity).toImage_bijective
          (gammaGroundRVRightTag_injective V.domain U.arity))).symm.injective))
  nonzero a i := by
    classical
    have ha : a.val ∈ (gammaGroundRVLeftTag U.domain V.arity).image.carrier ∨
        a.val ∈ (gammaGroundRVRightTag V.domain U.arity).image.carrier := a.property
    by_cases h : a.val ∈ (gammaGroundRVLeftTag U.domain V.arity).image.carrier
    · simpa only [GammaGroundMap.union, dite_eq_left h, GammaGroundMap.comp] using
        U.nonzero (gammaGroundRVUntagLeft U.domain V.arity ⟨a.val, h⟩) i
    · simpa only [GammaGroundMap.union, dite_eq_right h, GammaGroundMap.comp] using
        V.nonzero (gammaGroundRVUntagRight V.domain U.arity ⟨a.val, ha.resolve_left h⟩) i

theorem gammaGroundRVClass_coprod (U V : GammaGroundRVObject hc ground k) :
    gammaGroundRVClass (U.coprod V) = gammaGroundRVClass U + gammaGroundRVClass V := by
  let W := U.coprod V
  let X := (gammaGroundRVLeftTag U.domain V.arity).image
  let Y := (gammaGroundRVRightTag V.domain U.arity).image
  have hX : X.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  have hY : Y.carrier ⊆ W.domain.carrier := fun _ h => Or.inr h
  have hdiff : (W.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp (gammaGroundRVTaggedImages_disjoint U.domain V.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX :=
    ⟨(gammaGroundRVLeftTag U.domain V.arity).toImage, (gammaGroundRVLeftTag U.domain V.arity).toImage_bijective (gammaGroundRVLeftTag_injective U.domain V.arity)⟩
  let G := (gammaGroundRVRightTag V.domain U.arity).toImage
  let gmap : GammaGroundMap V.domain (W.domain.sdiff X) := G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply ((gammaGroundRVRightTag V.domain U.arity).toImage_bijective (gammaGroundRVRightTag_injective V.domain U.arity)).injective
      exact Subtype.ext (congrArg (fun x : W.domain.sdiff X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.domain.sdiff X) (fun _ h => h.1) := ⟨gmap, hg⟩
  have hs := gammaGroundRVClass_scissor W X hX
  rw [← gammaGroundRVClass_iso (asIso f), ← gammaGroundRVClass_iso (asIso g)] at hs
  exact hs.symm

theorem gammaGroundRVClass_surjective : Function.Surjective (gammaGroundRVClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundRVPresentation hc ground k) GammaGroundRVObject.coprod gammaGroundRVClass_coprod

end DiamondIntegral.Section3
