import IntegrationSection5.FixedVFFiniteImage
import IntegrationSection5.ScalarCoordinateRefinement
import IntegrationSection5.RVContractionMaps

/-! Finite output volumes for the actual contraction of a mixed map in
arbitrary VF arity. The proof fixes one representative of the input RV
volume and applies RV-to-VF finiteness to each output coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m u l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u l}

theorem mixed_vf_fibre_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f))
    (x : Fin n → VF (M := M)) :
    {y : Fin u → VF (M := M) | ∃ a : A, a.val.1 = x ∧ (f a).val.1 = y}.Finite := by
  let D (i : Fin u) := {y : VF (M := M) | ∃ a : A, a.val.1 = x ∧ vfAt (f a).val i = y}
  have hD (i : Fin u) : (D i).Finite :=
    fixed_vf_scalar_image_finite hκ hs G hsmall (carrier A) (fun a => vfAt (f a).val i)
      (gamma_scalar_coordinate f hf i) x
  apply (Set.Finite.pi hD).subset
  rintro y ⟨a,ha,rfl⟩ i _
  exact ⟨a,ha,rfl⟩

theorem mixed_rvContractionMap_finite_volume_images {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {B : DefSet (M := M) S n l} (f : Map A B) (hc : Contractible f)
    (hA : IsRVPullback (carrier A)) (hf : GammaGraphDefinable G (pointMapGraph f))
    (t : Fin n → RV (M := M)) :
    (@SpecialTransformations.Section4.RVObject.volumeFibreImage M (@CanonicalStructure.normalize M sM) S n
      (pullbackObject A) (pullbackObject B) (rvContractionMap f hc) t).Finite := by
  choose x hx using fun i => CanonicalRV.encodedRv_surjective (t i)
  have hFin := (mixed_vf_fibre_image_finite hκ hs hsmall f hf x).image
    (fun y : Fin n → VF (M := M) => fun i => rv (y i))
  apply hFin.subset
  rintro s ⟨v,ht,hv⟩
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective A v
  change (rvObjectVolume (pullbackObject A) (Map.toImage (rawKeyMap A) a)).val = t at ht
  rw [pullbackObject_value_key] at ht
  let p : Point (M := M) n m := (x,a.val.2)
  have hcell : SameRV p a.val := by
    apply (sameRV_iff _ _).mpr
    refine ⟨fun i => ?_,rfl⟩
    exact (hx i).trans (congrFun ht i).symm
  let b : A := ⟨p,(isRVPullback_iff _).mp hA a.val a.property p hcell.symm⟩
  have hKey : Map.toImage (rawKeyMap A) b = Map.toImage (rawKeyMap A) a :=
    Subtype.ext ((rawKeyMap_eq_iff b a).mpr hcell)
  have hVolume := rvContractionMap_volume_spec f hc b
  rw [hKey] at hVolume
  change (rvObjectVolume (pullbackObject B)
    (rvContractionMap f hc (Map.toImage (rawKeyMap A) a))).val = s at hv
  refine ⟨(f b).val.1,⟨b,rfl,rfl⟩,?_⟩
  exact hVolume.symm.trans hv

end IntegrationInACVF.Section5
