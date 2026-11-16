import «section 6».EverywhereMeasuredLiftWeights

/-! For an actual lift of a measured RV map, its Gamma density ratio is
the value of the quotient of the target and source VF coordinate products.
No derivative or choice of VF representatives is required for this identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem measuredLift_density_value {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (f : Map (rvLift U.object) (rvLift V.object))
    (hlabel : ∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2) (p : rvLift U.object) :
    (gammaMapValue U.form (liftLabelMap U.object p) /
      gammaMapValue V.form (liftLabelMap V.object (f p))).val =
        vfValue ((∏ i,(f p).val.1 i) / ∏ i,p.val.1 i) := by
  have hTarget := liftLabelMap_target_of_graph e.iso.hom.map f hlabel p
  have h := congrArg (fun γ : Gamma M => γ.val) (e.gamma_jacobian (liftLabelMap U.object p))
  change (gammaMapValue U.form (liftLabelMap U.object p) /
    gammaMapValue V.form (e.iso.hom.map (liftLabelMap U.object p))).val =
      (V.volumeGamma (e.iso.hom.map (liftLabelMap U.object p)) / U.volumeGamma (liftLabelMap U.object p)).val at h
  rw [← hTarget] at h
  refine h.trans ?_
  have hP := rvLift_volume_gamma_value U p
  have hQ := rvLift_volume_gamma_value V (f p)
  change _ = Values.vfValueHom (_ / _)
  rw [map_div₀]
  have hDiv : (V.volumeGamma (liftLabelMap V.object (f p)) / U.volumeGamma (liftLabelMap U.object p)).val =
      (V.volumeGamma (liftLabelMap V.object (f p))).val / (U.volumeGamma (liftLabelMap U.object p)).val := by
    simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
  rw [hDiv,hP,hQ]
  rfl

end DiamondIntegral.Section6
