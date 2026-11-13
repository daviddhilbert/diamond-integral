import «section 3».MeasuredRVCoproducts

/-! Every fixed-degree measured positive class has a genuine measured
object representative. Addition is the actual tagged disjoint union. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem measuredRVClass_coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) :
    measuredRVClass hc (U.coprod hc V) = measuredRVClass hc U + measuredRVClass hc V := by
  let W := U.coprod hc V
  let X := (rvLeftTagMap U.underlying.domain V.underlying.arity).image
  let Y := (rvRightTagMap V.underlying.domain U.underlying.arity).image
  have hX : X.carrier ⊆ W.underlying.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.underlying.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (rvTaggedImages_disjoint U.underlying.domain V.underlying.domain) hx ht⟩
  let f : U ⟶ W.restrict hc X hX := {
    bijection := ⟨(rvLeftTagMap U.underlying.domain V.underlying.arity).toImage,
      rvLeftTagMap_toImage_bijective U.underlying.domain V.underlying.arity⟩
    preserves u := (measuredRVCoprod_combined_left hc U V u).symm }
  let G := (rvRightTagMap V.underlying.domain U.underlying.arity).toImage
  let gmap : Map V.underlying.domain (W.underlying.difference X) :=
    G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply (rvRightTagMap_toImage_bijective V.underlying.domain U.underlying.arity).injective
      exact Subtype.ext (congrArg (fun x : W.underlying.difference X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict hc (W.underlying.difference X) (fun _ h => h.1) := {
    bijection := ⟨gmap, hg⟩
    preserves v := (measuredRVCoprod_combined_right hc U V v).symm }
  have hs := measuredRVClass_scissor hc W X hX
  rw [← measuredRVClass_iso hc (asIso f), ← measuredRVClass_iso hc (asIso g)] at hs
  exact hs.symm

theorem measuredRVClass_surjective (hc : CanonicalStructure.IsCanonical (M := M)) :
    Function.Surjective (measuredRVClass (M := M) (S := S) (k := k) hc) :=
  PositiveAdditiveGrothendieck.of_surjective (measuredRVPresentation hc S k)
    (MeasuredRVObject.coprod hc) (measuredRVClass_coprod hc)

end DiamondIntegral.Section3
