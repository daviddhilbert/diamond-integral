import «section 3».VFProducts
import «section 3».VFScissors
import «section 3».CarrierBijections
import Section4.VFFiniteSemiring

/-! Genuine VF coproducts preserve both dimension bounds and finite RV
fibres. Their classes give all fixed-degree positive representatives. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {k : ℕ}

def VFObject.toCompanionFinite (U : VFObject (M := M) S k) : VFFiniteAllObject S :=
  ⟨U.toCompanionAll, U.finite⟩

def VFObject.coprod (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U V : VFObject (M := M) S k) : VFObject S k where
  vfArity := U.vfArity + V.vfArity
  rvArity := 1 + (U.rvArity + V.rvArity)
  domain := (vfAllCoprodObject U.toCompanionAll V.toCompanionAll).set
  dimension := (vfDimension_le_iff_companion hc hs hS hv _ _).mpr (by
    rw [vfDim_coprod hc hs hS (rawRVSpace 1) (rawRVSpace_rvCoded 1)]
    exact max_le ((vfDimension_le_iff_companion hc hs hS hv _ _).mp U.dimension)
      ((vfDimension_le_iff_companion hc hs hS hv _ _).mp V.dimension))
  finite := finiteRVFibres_coprod (U := U.toCompanionAll) (V := V.toCompanionAll) U.finite V.finite

theorem vfClass_coprod (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U V : VFObject (M := M) S k) :
    vfClass (U.coprod hc hs hS hv V) = vfClass U + vfClass V := by
  let W := U.coprod hc hs hS hv V
  let X := (mixedLeftTagMap U.domain V.vfArity V.rvArity).image
  let Y := (mixedRightTagMap V.domain U.vfArity U.rvArity).image
  have hX : X.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  have hdiff : (W.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp
        (mixedTaggedImages_disjoint U.domain V.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX :=
    ⟨(mixedLeftTagMap U.domain V.vfArity V.rvArity).toImage,
      mixedLeftTagMap_toImage_bijective _ _ _⟩
  let F := (mixedRightTagMap V.domain U.vfArity U.rvArity).toImage
  let gmap : Map V.domain (W.difference X) := F.corestrict (fun a => hdiff.ge (F a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply (mixedRightTagMap_toImage_bijective V.domain U.vfArity U.rvArity).injective
      exact Subtype.ext (congrArg (fun x : W.difference X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.difference X) (fun _ h => h.1) := ⟨gmap, hg⟩
  have h := vfClass_scissor W X hX
  rw [← vfClass_iso (asIso f), ← vfClass_iso (asIso g)] at h
  exact h.symm

theorem vfClass_surjective (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Function.Surjective (vfClass (M := M) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (vfPresentation S k)
    (VFObject.coprod hc hs hS hv) (vfClass_coprod hc hs hS hv)

end DiamondIntegral.Section3
