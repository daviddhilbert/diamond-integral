import «section 3».GammaGroundMeasuredRVCoproducts

/-! Every fixed-degree measured positive class has a genuine measured
object representative. Addition is the actual tagged disjoint union. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRVClass_coprod (U V : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVClass (U.coprod V) = gammaGroundMeasuredRVClass U + gammaGroundMeasuredRVClass V := by
  let W := U.coprod V
  let X := (gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).image
  let Y := (gammaGroundRVRightTag V.underlying.domain U.underlying.arity).image
  have hX : X.carrier ⊆ W.underlying.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.underlying.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (gammaGroundRVTaggedImages_disjoint U.underlying.domain V.underlying.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX := {
    bijection := ⟨(gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage,
      (gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage_bijective (gammaGroundRVLeftTag_injective U.underlying.domain V.underlying.arity)⟩
    preserves u := (gammaGroundMeasuredRVCoprod_combined_left U V u).symm }
  let G := (gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage
  let gmap : GammaGroundMap V.underlying.domain (W.underlying.domain.sdiff X) :=
    G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply ((gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage_bijective (gammaGroundRVRightTag_injective V.underlying.domain U.underlying.arity)).injective
      exact Subtype.ext (congrArg (fun x : W.underlying.domain.sdiff X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.underlying.domain.sdiff X) (fun _ h => h.1) := {
    bijection := ⟨gmap, hg⟩
    preserves v := (gammaGroundMeasuredRVCoprod_combined_right U V v).symm }
  have hs := gammaGroundMeasuredRVClass_scissor W X hX
  rw [← gammaGroundMeasuredRVClass_iso (asIso f), ← gammaGroundMeasuredRVClass_iso (asIso g)] at hs
  exact hs.symm

theorem gammaGroundMeasuredRVClass_surjective :
    Function.Surjective (gammaGroundMeasuredRVClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundMeasuredRVPresentation hc ground k)
    GammaGroundMeasuredRVObject.coprod gammaGroundMeasuredRVClass_coprod

end DiamondIntegral.Section3
