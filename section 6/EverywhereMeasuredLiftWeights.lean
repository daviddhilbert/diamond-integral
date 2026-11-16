import «section 6».EverywhereMeasuredRVLiftData
import «section 6».RVVolumeRatioMaps

/-! The measured full derivative identity is the structural product
ratio identity for every compatible presentation valuation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {S : Set M} {n : ℕ}

theorem EverywhereMeasuredRVLift.weighted_measure
    {U V : MeasuredRVObject (M := M) S n} {e : MeasuredRVIso U V}
    (f : EverywhereMeasuredRVLift e) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) (p : rvLift U.object) :
    ∃ L, HasMixedVFDerivativeAt f.map p L ∧ v (LinearMap.toMatrix' L).det =
      (∏ i,v ((f.map p).val.1 i)) / ∏ i,v (p.val.1 i) := by
  obtain ⟨L,hL,hJ⟩ := f.measure p
  have hTarget := liftLabelMap_target_of_graph e.iso.hom.map f.map f.labels p
  have h := congrArg (fun γ : Gamma M => γ.val) (e.gamma_jacobian (liftLabelMap U.object p))
  change (gammaMapValue U.form (liftLabelMap U.object p) /
    gammaMapValue V.form (e.iso.hom.map (liftLabelMap U.object p))).val =
      (V.volumeGamma (e.iso.hom.map (liftLabelMap U.object p)) /
        U.volumeGamma (liftLabelMap U.object p)).val at h
  rw [← hTarget] at h
  have hP := rvLift_volume_gamma_value U p
  have hQ := rvLift_volume_gamma_value V (f.map p)
  have hCanonical : vfValue (LinearMap.toMatrix' L).det =
      vfValue ((∏ i,(f.map p).val.1 i) / ∏ i,p.val.1 i) := by
    rw [hJ,h]
    change _ = Values.vfValueHom (_ / _)
    rw [map_div₀]
    have hDiv : (V.volumeGamma (liftLabelMap V.object (f.map p)) /
      U.volumeGamma (liftLabelMap U.object p)).val =
      (V.volumeGamma (liftLabelMap V.object (f.map p))).val /
        (U.volumeGamma (liftLabelMap U.object p)).val := by
      simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
    rw [hDiv,hP,hQ]
    rfl
  have hVal := (vfValue_eq_iff v hv _ _).mp hCanonical
  exact ⟨L,hL,by simpa only [map_div₀,map_prod] using hVal⟩

end DiamondIntegral.Section6
