import «section 6».RelativeMeasuredLiftRestrictions
import «section 6».RelativeMeasuredLiftGluing
import «section 6».MeasuredVFUnaryChainExtensions

/-! After replacing the exceptional label volumes, the remaining map
is one actual relatively unary measured VF lift: identity on exceptional
fibres and the original chosen lift on their complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def measuredRVVolumeExtensionTargetIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (B : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D B.object.domain)
    (hχ : Function.Injective χ) :
    MeasuredRVIso (measuredRVVolumeExtension hc U B D χ hχ) V where
  iso := rvIsoOfFiniteVolumeNonzero e.iso.hom.map (rvIso_map_bijective e.iso)
    (measuredRVVolumeExtension hc U B D χ hχ).finiteVolume V.finiteVolume
    (measuredRVVolumeExtension hc U B D χ hχ).nonzero V.nonzero
  balance u := (measuredRVVolumeExtension_totalWeight hc U B D χ hχ u).trans (e.balance u)

theorem exists_relative_measured_lift_after_volume_change
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f)
    (hlabel : ∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2)
    (active : Fin n) (hUnary : VFUnaryRelativeAt f active)
    (B : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : D.carrier ⊆ U.object.domain.carrier) (χ : Map D B.object.domain)
    (hχ : Function.Injective χ)
    (hVol : ∀ u : D,B.object.value (χ u) = V.object.value (e.iso.hom.map ⟨u.val,hD u.property⟩))
    (hGood : ∀ p : rvLift U.object,p.val.2 ∉ D.carrier →
      ∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap _ p) / gammaMapValue V.form (liftLabelMap _ (f p))).val) :
    ∃ G : EverywhereMeasuredRVLift (measuredRVVolumeExtensionTargetIso hc e B D χ hχ),
      VFUnaryRelativeAt G.map active := by
  let W := measuredRVVolumeExtension hc U B D χ hχ
  let d := measuredRVVolumeExtensionTargetIso hc e B D χ hχ
  let C := U.object.domain.sdiff D
  have hC : C.carrier ⊆ U.object.domain.carrier := Set.sdiff_subset
  obtain ⟨F,hFu,hAgree⟩ := exists_relative_measured_lift_restrict e f hf hlabel active hUnary C hC
    (fun p hp => hGood p hp.2)
  let a : MeasuredRVIso (W.restrict C hC) (U.restrict C hC) :=
    ⟨rvIsoOfFiniteVolumeNonzero (Map.id C) Function.bijective_id
      (W.restrict C hC).finiteVolume (U.restrict C hC).finiteVolume
      (W.restrict C hC).nonzero (U.restrict C hC).nonzero,
      fun u => measuredRVVolumeExtension_totalWeight hc U B D χ hχ ⟨u.val,hC u.property⟩⟩
  have haVol (u : C) :
      (U.restrict C hC).object.value (a.iso.hom.map u) = (W.restrict C hC).object.value u := by
    exact (measuredRVVolumeExtension_of_not_mem hc U B D χ hχ
      ⟨u.val,hC u.property⟩ u.property.2).symm
  let H := volumePreservingMeasuredRVLift a haVol
  let GGood : EverywhereMeasuredRVLift (d.restrict C hC) :=
    (H.comp F).changeIso (d.restrict C hC) (fun _ => rfl)
  have hGGood : VFUnaryRelativeAt GGood.map active := by
    intro p j hj
    exact (hFu (H.map p) j hj).trans rfl
  have hBadVol (u : D) :
      (V.restrict (d.iso.hom.map.restrict hD).image (rvLabelImage_subset d.iso D hD)).object.value
        ((d.restrict D hD).iso.hom.map u) = (W.restrict D hD).object.value u := by
    exact (hVol u).symm.trans
      (measuredRVVolumeExtension_of_mem hc U B D χ hχ ⟨u.val,hD u.property⟩ u.property).symm
  let GBad := volumePreservingMeasuredRVLift (d.restrict D hD) hBadVol
  let P : Bool → DefSet (rawRVSpace (M := M) U.object.arity) S := fun b => if b then D else C
  have hP : ∀ b,(P b).carrier ⊆ W.object.domain.carrier := by
    intro b
    cases b
    · exact hC
    · exact hD
  have hCover (u : W.object.domain) : ∃ b,u.val ∈ (P b).carrier := by
    by_cases hu : u.val ∈ D.carrier
    · exact ⟨true,hu⟩
    · exact ⟨false,u.property,hu⟩
  have hDisj (b c : Bool) (z) : z ∈ (P b).carrier → z ∈ (P c).carrier → b=c := by
    cases b <;> cases c
    · exact fun _ _ => rfl
    · exact fun hu hd => (hu.2 hd).elim
    · exact fun hd hu => (hu.2 hd).elim
    · exact fun _ _ => rfl
  let G : ∀ b,EverywhereMeasuredRVLift (d.restrict (P b) (hP b)) := fun b => by
    cases b
    · exact GGood
    · exact GBad
  have hGU : ∀ b,VFUnaryRelativeAt (G b).map active := by
    intro b
    cases b
    · exact hGGood
    · exact volumePreservingMeasuredRVLift_unary _ _ active
  exact exists_glued_relative_measured_lift d P hP hCover hDisj active G hGU

end DiamondIntegral.Section6
