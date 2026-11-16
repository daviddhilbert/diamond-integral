import «section 6».ExtendedLiftPiecePullbacks

/-! Extend an actual local VF lift to a fixed global old-label domain.
On the selected piece it uses the local lift through the prescribed
label injection; elsewhere the VF tuple and all labels are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def extendedLocalVFMap (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Map (rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD))
      (DefSet.univ (rawVFSpace (M := M) n) S) :=
  (Map.fst (rawVFSpace (M := M) n) (rawRVSpace B.object.arity) S (rvLift B.object)).comp
    (F.map.comp (extendedLiftPiecePullback hc U A D hD χ hχ))

def extendedLiftVFMap (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Map (rvLift (measuredRVVolumeExtension hc U A D χ hχ).object)
      (DefSet.univ (rawVFSpace (M := M) n) S) :=
  replaceMapOn (extendedLocalVFMap hc U F D hD χ hχ)
    (Map.fst (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S
      (rvLift (measuredRVVolumeExtension hc U A D χ hχ).object))

theorem extendedLiftVFMap_of_piece (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object)
    (q : rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)) (hpq : q.val = p.val) :
    (extendedLiftVFMap hc U F D hD χ hχ p).val =
      (F.map (extendedLiftPiecePullback hc U A D hD χ hχ q)).val.1 := by
  have hp : p.val ∈ (rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)).carrier :=
    hpq ▸ q.property
  change (replaceMapOn (extendedLocalVFMap hc U F D hD χ hχ) _ p).val = _
  rw [replaceMapOn_of_mem _ _ p hp]
  have he : (⟨p.val,hp⟩ : rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD)) = q :=
    Subtype.ext hpq.symm
  rw [he]
  rfl

theorem extendedLiftVFMap_of_not_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) (hp : p.val.2 ∉ D.carrier) :
    (extendedLiftVFMap hc U F D hD χ hχ p).val = p.val.1 := by
  change (replaceMapOn (extendedLocalVFMap hc U F D hD χ hχ) _ p).val = _
  rw [replaceMapOn_of_not_mem _ _ p (fun h => hp
    ((rvLift_restrict_mem_iff (measuredRVVolumeExtension hc U A D χ hχ).object D hD p.val).mp h).2)]
  rfl

theorem extendedLiftVFMap_volume (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) :
    (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ) ((rvIso_map_bijective e.iso).1.comp hχ)).object.value
      (liftLabelMap (measuredRVVolumeExtension hc U A D χ hχ).object p) =
        tupleRV (extendedLiftVFMap hc U F D hD χ hχ p).val := by
  let W := measuredRVVolumeExtension hc U A D χ hχ
  let u := liftLabelMap W.object p
  by_cases hp : p.val.2 ∈ D.carrier
  · let q : rvLift (W.object.restrict D hD) :=
      ⟨p.val,(rvLift_restrict_mem_iff W.object D hD p.val).mpr ⟨p.property,hp⟩⟩
    let a := extendedLiftPiecePullback hc U A D hD χ hχ q
    have hTag := liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels a
    rw [extendedLiftPiecePullback_label] at hTag
    have hVol := liftLabelMap_volume B.object (F.map a)
    rw [hTag] at hVol
    rw [extendedLiftVFMap_of_piece hc U F D hD χ hχ p q rfl,
      measuredRVVolumeExtension_of_mem hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ) u hp]
    exact hVol
  · rw [extendedLiftVFMap_of_not_mem hc U F D hD χ hχ p hp,
      measuredRVVolumeExtension_of_not_mem hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ) u hp]
    have hVol := liftLabelMap_volume W.object p
    rw [measuredRVVolumeExtension_of_not_mem hc U A D χ hχ u hp] at hVol
    exact hVol

def extendedMeasuredLiftMap (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    Map (rvLift (measuredRVVolumeExtension hc U A D χ hχ).object)
      (rvLift (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).object) :=
  ((extendedLiftVFMap hc U F D hD χ hχ).pair
    (Map.snd (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S
      (rvLift (measuredRVVolumeExtension hc U A D χ hχ).object))).corestrict (fun p =>
        ⟨liftLabelMap (measuredRVVolumeExtension hc U A D χ hχ).object p,rfl,
          extendedLiftVFMap_volume hc U F D hD χ hχ p⟩)

theorem extendedMeasuredLiftMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) :
    (extendedMeasuredLiftMap hc U F D hD χ hχ p).val =
      ((extendedLiftVFMap hc U F D hD χ hχ p).val,p.val.2) := rfl

end DiamondIntegral.Section6
