import «section 6».MeasuredRVHeadCovers
import «section 6».VFCoordinateReindexing

/-! Actual everywhere differentiable lifts of structural coordinate
permutations. Their derivative is the permutation linear map and has
Gamma value one, including the empty-coordinate case. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def vfReindexLinear (e : Equiv.Perm (Fin n)) : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M) :=
  Matrix.toLin' ((1 : Matrix (Fin n) (Fin n) (VF M)).submatrix e id)

theorem vfReindexLinear_apply (e : Equiv.Perm (Fin n)) (x : Fin n → VF M) :
    vfReindexLinear e x = x ∘ e := by
  funext i
  change ((1 : Matrix (Fin n) (Fin n) (VF M)).mulVec x) (e i) = x (e i)
  rw [Matrix.one_mulVec]

theorem vfValue_int_unit (u : ℤˣ) : vfValue (((u : ℤ) : VF M)) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [Units.val_one,Int.cast_one]
    exact Values.vf_value_one
  · change Values.vfValueHom (((-1 : ℤ) : VF M)) = 1
    rw [Int.cast_neg,Int.cast_one,vfValue_neg,map_one]

theorem vfReindexLinear_det_value (e : Equiv.Perm (Fin n)) :
    vfValue (LinearMap.toMatrix' (vfReindexLinear (M := M) e)).det = 1 := by
  rw [vfReindexLinear,LinearMap.toMatrix'_toLin',Matrix.det_permute,Matrix.det_one,mul_one]
  exact vfValue_int_unit (Equiv.Perm.sign e)

def reindexRVLiftMap (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Map (rvLift U) (rvLift (U.reindexVolume e)) :=
  (reindexVFMap (rvLift U) e).corestrict (fun p => by
    obtain ⟨u,hu,hVol⟩ := p.property
    exact ⟨u,hu,congrArg (fun t => t ∘ e) hVol⟩)

def reindexRVLiftInverseMap (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Map (rvLift (U.reindexVolume e)) (rvLift U) :=
  (reindexVFMap (rvLift (U.reindexVolume e)) e.symm).corestrict (fun p => by
    obtain ⟨u,hu,hVol⟩ := p.property
    refine ⟨u,hu,funext (fun i => ?_)⟩
    have h := congrFun hVol (e.symm i)
    change U.value u (e (e.symm i)) = _ at h
    rwa [e.apply_symm_apply] at h)

theorem reindexRVLiftMap_bijective (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    Function.Bijective (reindexRVLiftMap U e) := by
  have hLeft : Function.LeftInverse (reindexRVLiftInverseMap U e) (reindexRVLiftMap U e) := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg p.val.1 (e.apply_symm_apply i)
    · rfl
  have hRight : Function.RightInverse (reindexRVLiftInverseMap U e) (reindexRVLiftMap U e) := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg p.val.1 (e.symm_apply_apply i)
    · rfl
  exact ⟨hLeft.injective,hRight.surjective⟩

theorem reindexRVLiftMap_derivative (U : MeasuredRVObject (M := M) S n)
    (e : Equiv.Perm (Fin n)) (p : rvLift U.object) :
    HasMixedVFDerivativeAt (reindexRVLiftMap U.object e) p (vfReindexLinear e) := by
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift U p
  refine ⟨fun x => vfReindexLinear e x + 0,⟨ρ,fun x hx => ?_⟩,
    hasVFDerivativeAt_affine (vfReindexLinear e) 0 p.val.1⟩
  refine ⟨hρ x hx,?_⟩
  change (x ∘ e,p.val.2) = (vfReindexLinear e x + 0,p.val.2)
  rw [add_zero,vfReindexLinear_apply]

def measuredRVReindexIso (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    MeasuredRVIso U (U.reindexVolume e) where
  iso := rvReindexVolumeIso U.object e
  balance u := (U.reindexVolume_totalWeight e u).symm

def measuredRVReindexLift (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    EverywhereMeasuredRVLift (measuredRVReindexIso U e) where
  map := reindexRVLiftMap U.object e
  bijective := reindexRVLiftMap_bijective U.object e
  labels p := ⟨liftLabelMap U.object p,rfl,rfl⟩
  measure p := by
    refine ⟨vfReindexLinear e,reindexRVLiftMap_derivative U e p,?_⟩
    have hLabel : liftLabelMap (U.reindexVolume e).object (reindexRVLiftMap U.object e p) = liftLabelMap U.object p := by
      apply Subtype.ext
      rfl
    rw [vfReindexLinear_det_value,hLabel]
    change (1 : Values.GammaTop (M := M)) = (gammaMapValue U.form (liftLabelMap U.object p) /
      gammaMapValue U.form (liftLabelMap U.object p)).val
    rw [div_self']
    rfl

end DiamondIntegral.Section6
