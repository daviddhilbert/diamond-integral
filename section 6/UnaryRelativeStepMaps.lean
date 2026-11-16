import «section 6».UnaryRelativeApertureChains
import «section 6».UnaryRelativeApertureExistence
import «section 6».VariableReleaseTags

/-! A variable unary primitive followed by its required regularization.
The live output tag locus and its actual definable inverse to the old
live source are constructed from the old-label selector and branch tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def stepMap (D : UnaryRelativeApertureData A) := (regularization D.map.image).comp D.bijection

def stepPoint (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) := regularize (D.point p)

theorem stepMap_apply (D : UnaryRelativeApertureData A) (p : A) :
    (D.stepMap p).val=D.stepPoint p.val := rfl

theorem stepMap_bijective (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective D.stepMap := (regularization_bijective D.map.image).comp (D.bijective h00)

def stepOldLabels (_D : UnaryRelativeApertureData A) : Fin r → Fin (1+(1+r)) :=
  fun i => Fin.natAdd 1 (Fin.natAdd 1 i)

theorem stepOldLabels_at (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) :
    (D.stepPoint p).2 ∘ D.stepOldLabels=p.2 := by
  funext i
  simp only [stepPoint,stepOldLabels,regularize,point,Function.comp_apply,Fin.append_right]

theorem stepBranch_at (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) :
    (D.stepPoint p).2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1)))=branchTag (M := M) (D.core p) := by
  simp only [stepPoint,regularize,point,Fin.append_left,Fin.append_right]

def stepLiveTags (D : UnaryRelativeApertureData A) (U : DefSet (rawRVSpace (M := M) r) S) :
    DefSet (rawRVSpace (M := M) (1+(1+r))) S := by
  let V := selectedRVTagSet U D.stepOldLabels
  let W := rvBooleanTagSet S (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) false
  exact ⟨V.carrier ∩ W.carrier,V.definable.inter _ W.definable⟩

theorem stepLiveTags_at (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00)
    (U : DefSet (rawRVSpace (M := M) r) S) (p : Mixed M 1 r) :
    (D.stepPoint p).2 ∈ (D.stepLiveTags U).carrier ↔ p.2 ∈ U.carrier ∧ D.core p=false := by
  change ((D.stepPoint p).2 ∘ D.stepOldLabels ∈ U.carrier ∧
    (D.stepPoint p).2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1)))=branchTag (M := M) false) ↔ _
  rw [D.stepOldLabels_at,D.stepBranch_at]
  exact and_congr_right (fun _ => ⟨fun h => branchTag_injective h00 h,fun h => congrArg (branchTag (M := M)) h⟩)

def stepLiveInverse (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00)
    (U : DefSet (rawRVSpace (M := M) r) S) :
    Map (focusActive (regularizeMap D.map.image).image (D.stepLiveTags U)) (focusActive A U) := by
  let f := D.stepMap
  let hf := D.stepMap_bijective h00
  let g := (f.inverse hf).restrict
    (show (focusActive (regularizeMap D.map.image).image (D.stepLiveTags U)).carrier ⊆
      (regularizeMap D.map.image).image.carrier from fun _ hp => hp.1)
  refine g.corestrict (fun p => ?_)
  refine ⟨(g p).property,?_⟩
  have he : D.stepPoint (g p).val=p.val := congrArg Subtype.val (Map.apply_inverse f hf ⟨p.val,p.property.1⟩)
  have hU : (D.stepPoint (g p).val).2 ∈ (D.stepLiveTags U).carrier := by
    rw [he]
    exact p.property.2
  exact ((D.stepLiveTags_at h00 U (g p).val).mp hU).1

theorem stepLiveInverse_point (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (p : focusActive (regularizeMap D.map.image).image (D.stepLiveTags U)) :
    D.stepPoint (D.stepLiveInverse h00 U p).val=p.val :=
  congrArg Subtype.val (Map.apply_inverse D.stepMap (D.stepMap_bijective h00) ⟨p.val,p.property.1⟩)

theorem stepLiveInverse_noncore (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (p : focusActive (regularizeMap D.map.image).image (D.stepLiveTags U)) :
    D.core (D.stepLiveInverse h00 U p).val=false := by
  apply ((D.stepLiveTags_at h00 U _).mp ?_).2
  rw [D.stepLiveInverse_point h00 U p]
  exact p.property.2

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem stepChain (D : UnaryRelativeApertureData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) :
    UnaryRelativeApertureChain (G := G) A (regularizeMap D.map.image).image D.stepMap :=
  .comp (.relative A D) (.original (.regularize D.map.image
    (D.image_properInvariant h00 hc hκ hs hv hsmall) (D.image_vfDoublyBounded hc hs hsmall)))

end DiamondIntegral.Section6.UnaryRelativeApertureData
