import «section 6».RVReindexingLifts
import «section 6».EverywhereMeasuredLiftCovers

/-! Everywhere measured lifts transfer through separate source and
target coordinate permutations, retaining the exact original label map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def EverywhereMeasuredRVLift.changeIso {U V : MeasuredRVObject (M := M) S n}
    {d : MeasuredRVIso U V} (F : EverywhereMeasuredRVLift d) (e : MeasuredRVIso U V)
    (he : ∀ u,d.iso.hom.map u = e.iso.hom.map u) : EverywhereMeasuredRVLift e where
  map := F.map
  bijective := F.bijective
  labels p := by
    obtain ⟨u,hu,hv⟩ := F.labels p
    exact ⟨u,hu,(congrArg Subtype.val (he u)).symm.trans hv⟩
  measure := F.measure

theorem reindexRVLiftInverseMap_bijective (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Function.Bijective (reindexRVLiftInverseMap U e) := by
  have hL : Function.LeftInverse (reindexRVLiftMap U e) (reindexRVLiftInverseMap U e) := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg p.val.1 (e.symm_apply_apply i)
    · rfl
  have hR : Function.RightInverse (reindexRVLiftMap U e) (reindexRVLiftInverseMap U e) := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg p.val.1 (e.apply_symm_apply i)
    · rfl
  exact ⟨hL.injective,hR.surjective⟩

theorem reindexRVLiftInverseMap_derivative (U : MeasuredRVObject (M := M) S n)
    (e : Equiv.Perm (Fin n)) (p : rvLift (U.reindexVolume e).object) :
    HasMixedVFDerivativeAt (reindexRVLiftInverseMap U.object e) p (vfReindexLinear e.symm) := by
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift (U.reindexVolume e) p
  refine ⟨fun x => vfReindexLinear e.symm x + 0,⟨ρ,fun x hx => ?_⟩,
    hasVFDerivativeAt_affine (vfReindexLinear e.symm) 0 p.val.1⟩
  refine ⟨hρ x hx,?_⟩
  change (x ∘ e.symm,p.val.2) = (vfReindexLinear e.symm x + 0,p.val.2)
  rw [add_zero,vfReindexLinear_apply]

theorem measuredRVReindexIso_inv_map (U : MeasuredRVObject (M := M) S n)
    (e : Equiv.Perm (Fin n)) (u : U.object.domain) : (measuredRVReindexIso U e).iso.inv.map u = u := by
  have h := SpecialTransformations.Section7.rvIso_inv_apply (measuredRVReindexIso U e).iso u
  change (measuredRVReindexIso U e).iso.inv.map u = u at h
  exact h

def measuredRVReindexInverseLift (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    EverywhereMeasuredRVLift (measuredRVReindexIso U e).symm where
  map := reindexRVLiftInverseMap U.object e
  bijective := reindexRVLiftInverseMap_bijective U.object e
  labels p := ⟨liftLabelMap (U.reindexVolume e).object p,rfl,
    congrArg Subtype.val (measuredRVReindexIso_inv_map U e _)⟩
  measure p := by
    refine ⟨vfReindexLinear e.symm,reindexRVLiftInverseMap_derivative U e p,?_⟩
    have hLabel : liftLabelMap U.object (reindexRVLiftInverseMap U.object e p) =
        liftLabelMap (U.reindexVolume e).object p := Subtype.ext rfl
    rw [vfReindexLinear_det_value,hLabel]
    change (1 : Values.GammaTop (M := M)) =
      (gammaMapValue U.form (liftLabelMap (U.reindexVolume e).object p) /
        gammaMapValue U.form (liftLabelMap (U.reindexVolume e).object p)).val
    rw [div_self']
    rfl

def measuredRVReindexedIso {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (a b : Equiv.Perm (Fin n)) : MeasuredRVIso (U.reindexVolume a) (V.reindexVolume b) where
  iso := rvIsoOfFiniteVolumeNonzero e.iso.hom.map (rvIso_map_bijective e.iso)
    (U.reindexVolume a).finiteVolume (V.reindexVolume b).finiteVolume
    (U.reindexVolume a).nonzero (V.reindexVolume b).nonzero
  balance u := (U.reindexVolume_totalWeight a u).trans
    ((e.balance u).trans (V.reindexVolume_totalWeight b (e.iso.hom.map u)).symm)

def measuredRVUnreindexLift {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (a b : Equiv.Perm (Fin n)) (F : EverywhereMeasuredRVLift (measuredRVReindexedIso e a b)) :
    EverywhereMeasuredRVLift e :=
  (((measuredRVReindexLift U a).comp F).comp (measuredRVReindexInverseLift V b)).changeIso e
    (fun u => measuredRVReindexIso_inv_map V b (e.iso.hom.map u))

end DiamondIntegral.Section6
