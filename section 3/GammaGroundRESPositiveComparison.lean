import «section 3».GammaGroundRESScissors

/-! Finite source-value support survives genuine tagged disjoint unions.
The RES positive classes embed in RV before any groupification. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundRESClass_scissor (U : GammaGroundRESObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    gammaGroundRESClass (U.restrict X hX) +
      gammaGroundRESClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = gammaGroundRESClass U := by
  have hs := positiveClass_scissor (gammaGroundRESPresentation hc ground k)
    (show (gammaGroundRESPresentation hc ground k).scissor (U.restrict X hX)
      (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) U (GammaGroundRESObject.empty hc ground k) from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change gammaGroundRESClass _ + gammaGroundRESClass _ = gammaGroundRESClass _ + gammaGroundRESClass _ at hs
  simpa only [gammaGroundRESClass_empty, add_zero] using hs

theorem gammaGroundRESClass_coprod (U V : GammaGroundRESObject hc ground k) :
    gammaGroundRESClass (U.coprod V) = gammaGroundRESClass U + gammaGroundRESClass V := by
  let W := U.coprod V
  let X := (gammaGroundRVLeftTag U.obj.domain V.obj.arity).image
  let Y := (gammaGroundRVRightTag V.obj.domain U.obj.arity).image
  have hX : X.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inl h
  have hY : Y.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inr h
  have hdiff : (W.obj.domain.sdiff X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp (gammaGroundRVTaggedImages_disjoint U.obj.domain V.obj.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX :=
    ObjectProperty.homMk ⟨(gammaGroundRVLeftTag U.obj.domain V.obj.arity).toImage,
      (gammaGroundRVLeftTag U.obj.domain V.obj.arity).toImage_bijective (gammaGroundRVLeftTag_injective U.obj.domain V.obj.arity)⟩
  let G := (gammaGroundRVRightTag V.obj.domain U.obj.arity).toImage
  let gmap : GammaGroundMap V.obj.domain (W.obj.domain.sdiff X) := G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply ((gammaGroundRVRightTag V.obj.domain U.obj.arity).toImage_bijective (gammaGroundRVRightTag_injective V.obj.domain U.obj.arity)).injective
      exact Subtype.ext (congrArg (fun x : W.obj.domain.sdiff X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.obj.domain.sdiff X) (fun _ h => h.1) := ObjectProperty.homMk ⟨gmap, hg⟩
  have hs := gammaGroundRESClass_scissor W X hX
  rw [← gammaGroundRESClass_iso ((gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso f.hom)), ← gammaGroundRESClass_iso ((gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).isoMk (asIso g.hom))] at hs
  exact hs.symm

theorem gammaGroundRESClass_surjective : Function.Surjective (gammaGroundRESClass (M := M) (hc := hc) (ground := ground) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (gammaGroundRESPresentation hc ground k) GammaGroundRESObject.coprod gammaGroundRESClass_coprod


theorem gammaGroundRESClass_eq_iff_iso {U V : GammaGroundRESObject hc ground k} :
    gammaGroundRESClass U = gammaGroundRESClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he := congrArg gammaGroundRESToRVKPlus h
    rw [gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class] at he
    obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp he
    exact ⟨(gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩
  · rintro ⟨e⟩
    exact gammaGroundRESClass_iso e

theorem gammaGroundRESToRVKPlus_injective :
    Function.Injective (gammaGroundRESToRVKPlus (M := M) (hc := hc) (ground := ground) (k := k)) := by
  intro a b he
  obtain ⟨U, rfl⟩ := gammaGroundRESClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRESClass_surjective b
  rw [gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class] at he
  obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp he
  exact gammaGroundRESClass_iso ((gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).isoMk e)

end DiamondIntegral.Section3
