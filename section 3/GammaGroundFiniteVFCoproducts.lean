import «section 3».GammaGroundMixedTags
import «section 3».GammaGroundFiniteVFScissors
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

def GammaGroundFiniteVFObject.coprod (U V : GammaGroundFiniteVFObject hc ground) :
    GammaGroundFiniteVFObject hc ground where
  vfArity := U.vfArity + V.vfArity
  rvArity := 1 + (U.rvArity + V.rvArity)
  domain := (gammaGroundMixedLeftTag U.domain V.vfArity V.rvArity).image.union
    (gammaGroundMixedRightTag V.domain U.vfArity U.rvArity).image
  finite a := (gammaGroundFiniteRVFibres_leftTag U.domain _ _ U.finite a).union
    (gammaGroundFiniteRVFibres_rightTag V.domain _ _ V.finite a)

theorem gammaGroundFiniteVFClass_coprod (U V : GammaGroundFiniteVFObject hc ground) :
    gammaGroundFiniteVFClass (U.coprod V) = gammaGroundFiniteVFClass U + gammaGroundFiniteVFClass V := by
  let W := U.coprod V
  let X := (gammaGroundMixedLeftTag U.domain V.vfArity V.rvArity).image
  let Y := (gammaGroundMixedRightTag V.domain U.vfArity U.rvArity).image
  have hX : X.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (gammaGroundMixedTaggedImages_disjoint U.domain V.domain) hx ht⟩
  let F := (gammaGroundMixedLeftTag U.domain V.vfArity V.rvArity).toImage
  let f : U ⟶ W.restrict X hX :=
    ⟨F, (gammaGroundMixedLeftTag U.domain _ _).toImage_bijective
      (gammaGroundMixedLeftTag_injective U.domain _ _)⟩
  let G := (gammaGroundMixedRightTag V.domain U.vfArity U.rvArity).toImage
  let gmap : GammaGroundMap V.domain (W.domain.sdiff X) := G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply ((gammaGroundMixedRightTag V.domain U.vfArity U.rvArity).toImage_bijective
        (gammaGroundMixedRightTag_injective V.domain U.vfArity U.rvArity)).injective
      exact Subtype.ext (congrArg (fun x : W.domain.sdiff X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.domain.sdiff X) (fun _ h => h.1) := ⟨gmap, hg⟩
  have h := gammaGroundFiniteVFClass_scissor W X hX
  rw [← gammaGroundFiniteVFClass_iso (asIso f), ← gammaGroundFiniteVFClass_iso (asIso g)] at h
  exact h.symm

theorem gammaGroundFiniteVFClass_surjective :
    Function.Surjective (gammaGroundFiniteVFClass (M := M) (hc := hc) (ground := ground)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundFiniteVFPresentation hc ground)
    GammaGroundFiniteVFObject.coprod gammaGroundFiniteVFClass_coprod

end DiamondIntegral.Section3
