import «section 3».GammaGroundMeasuredRVProductLaws
import «section 3».GammaGroundMeasuredRVProductMorphisms
import «section 3».GammaGroundMeasuredRVIsomorphismClasses
import «section 3».GammaGroundRVProductScissors

/-! Actual measured products respect inherited cuts and partitions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundMeasuredRVProductRestrictionHom (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l)
    (B : GammaGroundDefSet hc ground (rawRVSpace (M := M) V.underlying.arity))
    (hB : B.carrier ⊆ V.underlying.domain.carrier) :
    GammaGroundMeasuredRVHom (U.product (V.restrict B hB))
      ((U.product V).restrict (gammaGroundRVProductDomain U.underlying.domain B)
        (gammaGroundRVProductRestrictionSubset U.underlying V.underlying B hB)) where
  bijection := GammaGroundBijection.id _
  preserves p := by
    obtain ⟨a, b, rfl⟩ := exists_gammaGroundRVPackPair U.underlying.domain B p
    change _ = (U.product V).combinedWeight
      (gammaGroundRVPackPair U.underlying.domain V.underlying.domain a ⟨b.val, hB b.property⟩)
    exact (GammaGroundMeasuredRVObject.product_combined_pair U (V.restrict B hB) a b).trans
      (GammaGroundMeasuredRVObject.product_combined_pair U V a ⟨b.val, hB b.property⟩).symm

theorem gammaGroundMeasuredRVClass_partition (U : GammaGroundMeasuredRVObject hc ground k)
    (A B : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.arity))
    (hA : A.carrier ⊆ U.underlying.domain.carrier) (hB : B.carrier ⊆ U.underlying.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) (he : (A.union B).carrier = U.underlying.domain.carrier) :
    gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass (U.restrict A hA) + gammaGroundMeasuredRVClass (U.restrict B hB) := by
  have hdiff : (U.underlying.domain.sdiff A).carrier = B.carrier := by
    ext a
    constructor
    · rintro ⟨ha, hn⟩
      exact (he.ge ha).resolve_left hn
    · intro hb
      exact ⟨hB hb, fun ha => Set.disjoint_left.mp hd ha hb⟩
  have hcut := gammaGroundMeasuredRVClass_scissor U A hA
  let f : GammaGroundMeasuredRVHom (U.restrict (U.underlying.domain.sdiff A) (fun _ h => h.1)) (U.restrict B hB) :=
    ⟨GammaGroundBijection.ofCarrierEq hdiff, fun _ => rfl⟩
  rw [gammaGroundMeasuredRVClass_iso (asIso f)] at hcut
  exact hcut.symm

def gammaGroundMeasuredRVCoprodLeftRestrictionHom (U V : GammaGroundMeasuredRVObject hc ground k) :
    GammaGroundMeasuredRVHom U ((U.coprod V).restrict
      (gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).image (fun _ h => Or.inl h)) where
  bijection := ⟨(gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage,
    (gammaGroundRVLeftTag U.underlying.domain V.underlying.arity).toImage_bijective
      (gammaGroundRVLeftTag_injective U.underlying.domain V.underlying.arity)⟩
  preserves a := (gammaGroundMeasuredRVCoprod_combined_left U V a).symm

def gammaGroundMeasuredRVCoprodRightRestrictionHom (U V : GammaGroundMeasuredRVObject hc ground k) :
    GammaGroundMeasuredRVHom V ((U.coprod V).restrict
      (gammaGroundRVRightTag V.underlying.domain U.underlying.arity).image (fun _ h => Or.inr h)) where
  bijection := ⟨(gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage,
    (gammaGroundRVRightTag V.underlying.domain U.underlying.arity).toImage_bijective
      (gammaGroundRVRightTag_injective V.underlying.domain U.underlying.arity)⟩
  preserves a := (gammaGroundMeasuredRVCoprod_combined_right U V a).symm

theorem gammaGroundMeasuredRVClass_product_coprod (U : GammaGroundMeasuredRVObject hc ground k)
    (V W : GammaGroundMeasuredRVObject hc ground l) :
    gammaGroundMeasuredRVClass (U.product (V.coprod W)) =
      gammaGroundMeasuredRVClass (U.product V) + gammaGroundMeasuredRVClass (U.product W) := by
  let T := V.coprod W
  let B := (gammaGroundRVLeftTag V.underlying.domain W.underlying.arity).image
  let D := (gammaGroundRVRightTag W.underlying.domain V.underlying.arity).image
  have hB : B.carrier ⊆ T.underlying.domain.carrier := fun _ h => Or.inl h
  have hD : D.carrier ⊆ T.underlying.domain.carrier := fun _ h => Or.inr h
  have hp := gammaGroundMeasuredRVClass_partition (U.product T)
    (gammaGroundRVProductDomain U.underlying.domain B) (gammaGroundRVProductDomain U.underlying.domain D)
    (gammaGroundRVProductRestrictionSubset U.underlying T.underlying B hB)
    (gammaGroundRVProductRestrictionSubset U.underlying T.underlying D hD)
    (gammaGroundRVProductDomain_disjoint _ _ _ (gammaGroundRVTaggedImages_disjoint _ _))
    (by rw [← gammaGroundRVProductDomain_union]; rfl)
  let f := (gammaGroundMeasuredRVProductRestrictionHom U T B hB).comp
    (gammaGroundMeasuredRVProductHom (GammaGroundMeasuredRVHom.id U) (gammaGroundMeasuredRVCoprodLeftRestrictionHom V W))
  let g := (gammaGroundMeasuredRVProductRestrictionHom U T D hD).comp
    (gammaGroundMeasuredRVProductHom (GammaGroundMeasuredRVHom.id U) (gammaGroundMeasuredRVCoprodRightRestrictionHom V W))
  exact hp.trans (congrArg₂ (· + ·) (gammaGroundMeasuredRVClass_iso (asIso f)).symm
    (gammaGroundMeasuredRVClass_iso (asIso g)).symm)

end DiamondIntegral.Section3
