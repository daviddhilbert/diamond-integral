import «section 3».MeasuredRVIsomorphismClasses
import «section 3».RESCoproducts

/-! Finite source-value support is closed under measured disjoint union.
The fixed-degree measured RES positive quotient injects into measured RV. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def MeasuredRESObject.coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRESObject (M := M) S k) : MeasuredRESObject S k :=
  ⟨U.obj.coprod hc V.obj, RVObject.coprod_res U.property V.property⟩

theorem measuredResClass_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRESObject (M := M) S k} (e : U ≅ V) :
    measuredResClass hc U = measuredResClass hc V := positiveClass_iso (measuredRESPresentation hc S k) ⟨e⟩

@[simp] theorem measuredResClass_empty (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredResClass hc (MeasuredRESObject.empty (M := M) S k) = 0 :=
  positiveClass_empty (measuredRESPresentation hc S k)

theorem measuredResClass_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) :
    measuredResClass hc (U.restrict hc X hX) +
      measuredResClass hc (U.restrict hc (U.obj.underlying.difference X) (fun _ h => h.1)) =
        measuredResClass hc U := by
  have hs := positiveClass_scissor (measuredRESPresentation hc S k)
    (show (measuredRESPresentation hc S k).scissor (U.restrict hc X hX)
      (U.restrict hc (U.obj.underlying.difference X) (fun _ h => h.1)) U (MeasuredRESObject.empty S k) from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change measuredResClass hc _ + measuredResClass hc _ = measuredResClass hc _ + measuredResClass hc _ at hs
  simpa only [measuredResClass_empty, add_zero] using hs

theorem measuredResClass_coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRESObject (M := M) S k) :
    measuredResClass hc (U.coprod hc V) = measuredResClass hc U + measuredResClass hc V := by
  let W := U.coprod hc V
  let X := (rvLeftTagMap U.obj.underlying.domain V.obj.underlying.arity).image
  let Y := (rvRightTagMap V.obj.underlying.domain U.obj.underlying.arity).image
  have hX : X.carrier ⊆ W.obj.underlying.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.obj.underlying.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (rvTaggedImages_disjoint U.obj.underlying.domain V.obj.underlying.domain) hx ht⟩
  let f : U ⟶ W.restrict hc X hX := ObjectProperty.homMk {
    bijection := ⟨(rvLeftTagMap U.obj.underlying.domain V.obj.underlying.arity).toImage,
      rvLeftTagMap_toImage_bijective U.obj.underlying.domain V.obj.underlying.arity⟩
    preserves u := (measuredRVCoprod_combined_left hc U.obj V.obj u).symm }
  let G := (rvRightTagMap V.obj.underlying.domain U.obj.underlying.arity).toImage
  let gmap : Map V.obj.underlying.domain (W.obj.underlying.difference X) :=
    G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply (rvRightTagMap_toImage_bijective V.obj.underlying.domain U.obj.underlying.arity).injective
      exact Subtype.ext (congrArg (fun x : W.obj.underlying.difference X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict hc (W.obj.underlying.difference X) (fun _ h => h.1) := ObjectProperty.homMk {
    bijection := ⟨gmap, hg⟩
    preserves v := (measuredRVCoprod_combined_right hc U.obj V.obj v).symm }
  have hs := measuredResClass_scissor hc W X hX
  rw [← measuredResClass_iso hc ((measuredResProperty S k).isoMk (asIso f.hom)),
    ← measuredResClass_iso hc ((measuredResProperty S k).isoMk (asIso g.hom))] at hs
  exact hs.symm

theorem measuredResClass_surjective (hc : CanonicalStructure.IsCanonical (M := M)) :
    Function.Surjective (measuredResClass (M := M) (S := S) (k := k) hc) :=
  PositiveAdditiveGrothendieck.of_surjective (measuredRESPresentation hc S k)
    (MeasuredRESObject.coprod hc) (measuredResClass_coprod hc)

theorem measuredResClass_eq_iff_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRESObject (M := M) S k} : measuredResClass hc U = measuredResClass hc V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he := congrArg (measuredResToRVKPlus hc) h
    rw [measuredResToRVKPlus_class, measuredResToRVKPlus_class] at he
    obtain ⟨e⟩ := measuredRVClass_eq_iff_iso.mp he
    exact ⟨(measuredResProperty S k).isoMk e⟩
  · rintro ⟨e⟩
    exact measuredResClass_iso hc e

theorem measuredResToRVKPlus_injective (hc : CanonicalStructure.IsCanonical (M := M)) :
    Function.Injective (measuredResToRVKPlus (M := M) (S := S) (k := k) hc) := by
  intro a b he
  obtain ⟨U, rfl⟩ := measuredResClass_surjective hc a
  obtain ⟨V, rfl⟩ := measuredResClass_surjective hc b
  rw [measuredResToRVKPlus_class, measuredResToRVKPlus_class] at he
  obtain ⟨e⟩ := measuredRVClass_eq_iff_iso.mp he
  exact measuredResClass_iso hc ((measuredResProperty S k).isoMk e)

end DiamondIntegral.Section3
