import «section 3».MeasuredRVProductLaws
import «section 3».MeasuredRVIsomorphismClasses
import Section4.RVProductRestrictions

/-! Products respect inherited measured cuts and disjoint partitions. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def measuredRVProductRestrictionHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l)
    (B : DefSet (rawRVSpace (M := M) V.underlying.arity) S)
    (hB : B.carrier ⊆ V.underlying.domain.carrier) :
    MeasuredRVHom (U.product hc (V.restrict hc B hB))
      ((U.product hc V).restrict hc (rvProductDomain U.underlying.domain B)
        (rvProductRestrictionSubset U.underlying.toCompanion.obj V.underlying.toCompanion.obj B hB)) where
  bijection := DefinableBijection.id _
  preserves p := by
    obtain ⟨a, b, rfl⟩ := exists_rvPackPair U.underlying.domain B p
    change _ = (U.product hc V).combinedWeight
      (rvPackPair U.underlying.domain V.underlying.domain a ⟨b.val, hB b.property⟩)
    exact (MeasuredRVObject.product_combined_pair hc U (V.restrict hc B hB) a b).trans
      (MeasuredRVObject.product_combined_pair hc U V a ⟨b.val, hB b.property⟩).symm

theorem measuredRVClass_partition (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.underlying.arity) S)
    (hA : A.carrier ⊆ U.underlying.domain.carrier) (hB : B.carrier ⊆ U.underlying.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) (he : (A.union B).carrier = U.underlying.domain.carrier) :
    measuredRVClass hc U = measuredRVClass hc (U.restrict hc A hA) +
      measuredRVClass hc (U.restrict hc B hB) := by
  let W : MeasuredRVMapObject hc S k := ⟨U⟩
  let e := (measuredRVCoprodUnionIso W A B hA hB hd).trans
    (measuredRVMapIsoOfHom (U := W.restrict (A.union B) (measuredRVUnionSubset W A B hA hB))
      (V := W) (measuredRVRestrictionIsoOfCarrierEq U (A.union B) _ he))
  have hi := measuredRVClass_iso hc (asIso (show
    ((U.restrict hc A hA).coprod hc (U.restrict hc B hB)) ⟶ U from measuredRVHomOfMapIso e))
  rw [measuredRVClass_coprod] at hi
  exact hi.symm

def measuredRVCoprodLeftRestrictionHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) :
    MeasuredRVHom U ((U.coprod hc V).restrict hc
      (rvLeftTagMap U.underlying.domain V.underlying.arity).image (fun _ h => Or.inl h)) where
  bijection := ⟨(rvLeftTagMap U.underlying.domain V.underlying.arity).toImage,
    rvLeftTagMap_toImage_bijective _ _⟩
  preserves a := (measuredRVCoprod_combined_left hc U V a).symm

def measuredRVCoprodRightRestrictionHom (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S k) :
    MeasuredRVHom V ((U.coprod hc V).restrict hc
      (rvRightTagMap V.underlying.domain U.underlying.arity).image (fun _ h => Or.inr h)) where
  bijection := ⟨(rvRightTagMap V.underlying.domain U.underlying.arity).toImage,
    rvRightTagMap_toImage_bijective _ _⟩
  preserves a := (measuredRVCoprod_combined_right hc U V a).symm

theorem measuredRVClass_product_coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V W : MeasuredRVObject (M := M) S l) :
    measuredRVClass hc (U.product hc (V.coprod hc W)) =
      measuredRVClass hc (U.product hc V) + measuredRVClass hc (U.product hc W) := by
  let T := V.coprod hc W
  let B := (rvLeftTagMap V.underlying.domain W.underlying.arity).image
  let D := (rvRightTagMap W.underlying.domain V.underlying.arity).image
  have hB : B.carrier ⊆ T.underlying.domain.carrier := fun _ h => Or.inl h
  have hD : D.carrier ⊆ T.underlying.domain.carrier := fun _ h => Or.inr h
  have he : (B.union D).carrier = T.underlying.domain.carrier := rfl
  have hp := measuredRVClass_partition hc (U.product hc T)
    (rvProductDomain U.underlying.domain B) (rvProductDomain U.underlying.domain D)
    (rvProductRestrictionSubset U.underlying.toCompanion.obj T.underlying.toCompanion.obj B hB)
    (rvProductRestrictionSubset U.underlying.toCompanion.obj T.underlying.toCompanion.obj D hD)
    (rvProductDomain_disjoint _ _ _ (rvTaggedImages_disjoint _ _))
    (by rw [← rvProductDomain_union]; rfl)
  let f := (measuredRVProductRestrictionHom hc U T B hB).comp
    (measuredRVProductHom hc (MeasuredRVHom.id U) (measuredRVCoprodLeftRestrictionHom hc V W))
  let g := (measuredRVProductRestrictionHom hc U T D hD).comp
    (measuredRVProductHom hc (MeasuredRVHom.id U) (measuredRVCoprodRightRestrictionHom hc V W))
  exact hp.trans (congrArg₂ (· + ·) (measuredRVClass_iso hc (asIso f)).symm
    (measuredRVClass_iso hc (asIso g)).symm)

end DiamondIntegral.Section3
