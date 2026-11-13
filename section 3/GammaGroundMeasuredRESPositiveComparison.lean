import «section 3».GammaGroundMeasuredRESScissors

/-! Finite source-value support is closed under measured disjoint union.
The fixed-degree measured RES positive quotient injects into measured RV. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRESClass_scissor     (U : GammaGroundMeasuredRESObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.underlying.arity))
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) :
    gammaGroundMeasuredRESClass (U.restrict X hX) +
      gammaGroundMeasuredRESClass (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1)) =
        gammaGroundMeasuredRESClass U := by
  have hs := positiveClass_scissor (gammaGroundMeasuredRESPresentation hc ground k)
    (show (gammaGroundMeasuredRESPresentation hc ground k).scissor (U.restrict X hX)
      (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1)) U (GammaGroundMeasuredRESObject.empty hc ground k) from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change gammaGroundMeasuredRESClass _ + gammaGroundMeasuredRESClass _ = gammaGroundMeasuredRESClass _ + gammaGroundMeasuredRESClass _ at hs
  simpa only [gammaGroundMeasuredRESClass_empty, add_zero] using hs

theorem gammaGroundMeasuredRESClass_coprod     (U V : GammaGroundMeasuredRESObject hc ground k) :
    gammaGroundMeasuredRESClass (U.coprod V) = gammaGroundMeasuredRESClass U + gammaGroundMeasuredRESClass V := by
  let W := U.coprod V
  let X := (gammaGroundRVLeftTag U.obj.underlying.domain V.obj.underlying.arity).image
  let Y := (gammaGroundRVRightTag V.obj.underlying.domain U.obj.underlying.arity).image
  have hX : X.carrier ⊆ W.obj.underlying.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.obj.underlying.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (gammaGroundRVTaggedImages_disjoint U.obj.underlying.domain V.obj.underlying.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX := ObjectProperty.homMk {
    bijection := ⟨(gammaGroundRVLeftTag U.obj.underlying.domain V.obj.underlying.arity).toImage,
      (gammaGroundRVLeftTag U.obj.underlying.domain V.obj.underlying.arity).toImage_bijective (gammaGroundRVLeftTag_injective U.obj.underlying.domain V.obj.underlying.arity)⟩
    preserves u := (gammaGroundMeasuredRVCoprod_combined_left U.obj V.obj u).symm }
  let G := (gammaGroundRVRightTag V.obj.underlying.domain U.obj.underlying.arity).toImage
  let gmap : GammaGroundMap V.obj.underlying.domain (W.obj.underlying.domain.sdiff X) :=
    G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply ((gammaGroundRVRightTag V.obj.underlying.domain U.obj.underlying.arity).toImage_bijective (gammaGroundRVRightTag_injective V.obj.underlying.domain U.obj.underlying.arity)).injective
      exact Subtype.ext (congrArg (fun x : W.obj.underlying.domain.sdiff X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.obj.underlying.domain.sdiff X) (fun _ h => h.1) := ObjectProperty.homMk {
    bijection := ⟨gmap, hg⟩
    preserves v := (gammaGroundMeasuredRVCoprod_combined_right U.obj V.obj v).symm }
  have hs := gammaGroundMeasuredRESClass_scissor W X hX
  rw [← gammaGroundMeasuredRESClass_iso ((gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso f.hom)),
    ← gammaGroundMeasuredRESClass_iso ((gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso g.hom))] at hs
  exact hs.symm

theorem gammaGroundMeasuredRESClass_surjective :
    Function.Surjective (gammaGroundMeasuredRESClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundMeasuredRESPresentation hc ground k)
    GammaGroundMeasuredRESObject.coprod (gammaGroundMeasuredRESClass_coprod)

theorem gammaGroundMeasuredRESClass_eq_iff_iso     {U V : GammaGroundMeasuredRESObject hc ground k} : gammaGroundMeasuredRESClass U = gammaGroundMeasuredRESClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he := congrArg (gammaGroundMeasuredRESToRVKPlus) h
    rw [gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class] at he
    obtain ⟨e⟩ := gammaGroundMeasuredRVClass_eq_iff_iso.mp he
    exact ⟨(gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact gammaGroundMeasuredRESClass_iso e

theorem gammaGroundMeasuredRESToRVKPlus_injective :
    Function.Injective (gammaGroundMeasuredRESToRVKPlus (M := M) (hc := hc) (ground := ground) (k := k)) := by
  intro a b he
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRESClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundMeasuredRESClass_surjective b
  rw [gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class] at he
  obtain ⟨e⟩ := gammaGroundMeasuredRVClass_eq_iff_iso.mp he
  exact gammaGroundMeasuredRESClass_iso ((gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).isoMk e)

end DiamondIntegral.Section3
