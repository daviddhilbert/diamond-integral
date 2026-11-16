import «section 6».FiniteVFSeparatedCores
import «section 6».PairedCenterOffsetMaps

/-! Paired prescribed core plans with only finite VF projections.
The original mixed centre families may have arbitrarily many RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} {E : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {hEA : E.carrier ⊆ A.carrier} {α β : Gamma M}
theorem matchedCenterImage_finite_vfProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hEA : E.carrier ⊆ A.carrier) (hEVF : (Prod.fst '' E.carrier).Finite) :
    (Prod.fst '' (matchedCenterImage f E hEA).carrier).Finite := by
  apply (unaryFieldImage_finite hc hκ hs hsmall f E.carrier hEVF).subset
  rintro x ⟨q,⟨p,hpq⟩,rfl⟩
  exact ⟨⟨p.val,hEA p.property⟩,p.property,congrArg Prod.fst hpq⟩

namespace SeparatedUnaryOffsetCores
variable (D : SeparatedUnaryOffsetCores f E hEA α β)
variable (hEVF : (Prod.fst '' E.carrier).Finite)
variable (hTargetVF : (Prod.fst '' (matchedCenterImage f E hEA).carrier).Finite)
variable (hSource : ∀ p : E,vfValue (p.val.1 0)<α.val)
variable (hTarget : ∀ p : E,vfValue ((f ⟨p.val,hEA p.property⟩).val.1 0)<β.val)

def sourcePlanFiniteVF : UnaryCorePlan A where
  centres := E
  subset := hEA
  finite_vf := hEVF
  offset := D.sourceOffset
  offset_nonzero := D.sourceNonzero
  source_bound p := (hSource p).trans (D.sourceFloor p)
  separated := D.sourceSeparated

def targetPlanFiniteVF (hf : Function.Injective f) : UnaryCorePlan B where
  centres := matchedCenterImage f E hEA
  subset := matchedCenterImage_subset f E hEA
  finite_vf := hTargetVF
  offset := matchedTargetOffsetMap f E hEA hf D.targetOffset
  offset_nonzero := matchedTargetOffsetMap_nonzero f E hEA hf D.targetOffset D.targetNonzero
  source_bound := by
    intro p
    obtain ⟨a,rfl⟩ := (matchedCenterMap_bijective f E hEA hf).surjective p
    rw [matchedTargetOffsetMap_at]
    exact (hTarget a).trans (D.targetFloor a)
  separated := by
    intro p q hpq
    obtain ⟨a,rfl⟩ := (matchedCenterMap_bijective f E hEA hf).surjective p
    obtain ⟨b,rfl⟩ := (matchedCenterMap_bijective f E hEA hf).surjective q
    have hab : a≠b := fun he => hpq (congrArg (matchedCenterMap f E hEA) he)
    simpa only [matchedTargetOffsetMap_at,matchedCenterMap_value] using D.targetSeparated a b hab

theorem targetPlanFiniteVF_disc_at (hf : Function.Injective f) (p : E) :
    (D.targetPlanFiniteVF hTargetVF hTarget hf).disc (matchedCenterMap f E hEA p)=
      unaryTaggedDisc (f ⟨p.val,hEA p.property⟩).val
        (finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p)) := by
  simp only [UnaryCorePlan.disc,UnaryCorePlan.radius,targetPlanFiniteVF,matchedTargetOffsetMap_at,matchedCenterMap_value]

theorem plans_disc_paired_finiteVF (hf : Function.Injective f) (p : E) (a : A) :
    a.val ∈ (D.sourcePlanFiniteVF hEVF hSource).disc p ↔
      (f a).val ∈ (D.targetPlanFiniteVF hTargetVF hTarget hf).disc (matchedCenterMap f E hEA p) := by
  rw [D.targetPlanFiniteVF_disc_at hTargetVF hTarget hf p]
  change (a.val.2=p.val.2 ∧ vfValue ((D.sourceOffset p).val 0)<vfValue (a.val.1 0-p.val.1 0)) ↔
    ((f a).val.2=(f ⟨p.val,hEA p.property⟩).val.2 ∧
      vfValue ((D.targetOffset p).val 0)<
        vfValue ((f a).val.1 0-(f ⟨p.val,hEA p.property⟩).val.1 0))
  have h := D.toUniformFinitePairedCores.mixed_image_iff f E hEA α β p (f a)
  constructor
  · rintro ⟨hTags,hClose⟩
    have hImage := h.mpr ⟨a,(mem_centeredGammaDisc _ _ _).mpr hClose,hTags,rfl⟩
    exact ⟨hImage.2,(mem_centeredGammaDisc _ _ _).mp hImage.1⟩
  · rintro ⟨hTags,hClose⟩
    obtain ⟨b,hb,hbTags,hba⟩ := h.mp ⟨(mem_centeredGammaDisc _ _ _).mpr hClose,hTags⟩
    have he : b=a := hf hba
    subst b
    exact ⟨hbTags,(mem_centeredGammaDisc _ _ _).mp hb⟩

end SeparatedUnaryOffsetCores
end DiamondIntegral.Section6
