import «section 6».FiniteRelativeMeasuredRVLifts

/-! Actual everywhere total-differentiable measured RV lifts and their
composition. Full total charts, rather than partial Jacobians, supply
the chain rule at every point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem mixedDerivative_comp {r s t : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S} (f : Map A B) (g : Map B C) (p : A)
    {L D : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hf : HasMixedVFDerivativeAt f p L) (hg : HasMixedVFDerivativeAt g (f p) D) :
    HasMixedVFDerivativeAt (g.comp f) p (D.comp L) := by
  obtain ⟨F,hF,hDF⟩ := hf
  obtain ⟨H,hH,hDH⟩ := hg
  have hDH' : HasVFDerivativeAt H (F p.val.1) D := hF.center.symm ▸ hDH
  exact ⟨H ∘ F,hF.comp hH hDF,hDH'.comp hDF⟩

structure EverywhereMeasuredRVLift {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) where
  map : Map (rvLift U.object) (rvLift V.object)
  bijective : Function.Bijective map
  labels : ∀ p, e.iso.hom.map.graph p.val.2 (map p).val.2
  measure : ∀ p, ∃ L, HasMixedVFDerivativeAt map p L ∧ vfValue (LinearMap.toMatrix' L).det =
    (gammaMapValue U.form (liftLabelMap U.object p) /
      gammaMapValue V.form (liftLabelMap V.object (map p))).val

def EverywhereMeasuredRVLift.comp {U V W : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso U V} {d : MeasuredRVIso V W}
    (F : EverywhereMeasuredRVLift e) (H : EverywhereMeasuredRVLift d) : EverywhereMeasuredRVLift (e.comp d) where
  map := H.map.comp F.map
  bijective := H.bijective.comp F.bijective
  labels p := by
    refine ⟨liftLabelMap U.object p,rfl,?_⟩
    have hF := liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels p
    have hH := liftLabelMap_target_of_graph d.iso.hom.map H.map H.labels (F.map p)
    rw [hF] at hH
    exact (congrArg Subtype.val hH).symm
  measure p := by
    obtain ⟨L,hL,hJ⟩ := F.measure p
    obtain ⟨D,hD,hK⟩ := H.measure (F.map p)
    refine ⟨D.comp L,mixedDerivative_comp F.map H.map p hL hD,?_⟩
    rw [LinearMap.toMatrix'_comp,Matrix.det_mul]
    change Values.vfValueHom (_*_) = _
    rw [map_mul]
    change vfValue (LinearMap.toMatrix' D).det * vfValue (LinearMap.toMatrix' L).det = _
    rw [hK,hJ]
    let a := gammaMapValue U.form (liftLabelMap U.object p)
    let b := gammaMapValue V.form (liftLabelMap V.object (F.map p))
    let c := gammaMapValue W.form (liftLabelMap W.object (H.map (F.map p)))
    change (b/c).val * (a/b).val = (a/c).val
    rw [← Values.gamma_val_mul]
    apply congrArg (fun z : Gamma M => z.val)
    simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]

def EverywhereMeasuredRVLift.identity (U : MeasuredRVObject (M := M) S n) :
    EverywhereMeasuredRVLift (MeasuredRVIso.identity U) where
  map := Map.id (rvLift U.object)
  bijective := Function.bijective_id
  labels p := ⟨liftLabelMap U.object p,rfl,rfl⟩
  measure p := by
    have hp0 (i : Fin n) : p.val.1 i ≠ 0 := by
      intro he
      have h := congrArg Subtype.val (congrFun (liftLabelMap_volume U.object p) i)
      change (U.object.value (liftLabelMap U.object p) i).val = (rv M (p.val.1 i)).val at h
      rw [he,rv_zero] at h
      exact U.nonzero (liftLabelMap U.object p) i h
    obtain ⟨δ,hδ⟩ := nonzero_tuple_rv_ball p.val.1 hp0
    refine ⟨LinearMap.id,⟨fun x => x+0,⟨δ,fun x hx => ?_⟩,
      hasVFDerivativeAt_affine LinearMap.id 0 p.val.1⟩,?_⟩
    · refine ⟨⟨liftLabelMap U.object p,rfl,(liftLabelMap_volume U.object p).trans (hδ x hx).symm⟩,?_⟩
      simp only [add_zero]
      rfl
    · rw [LinearMap.toMatrix'_id,Matrix.det_one]
      change vfValue 1 = (gammaMapValue U.form (liftLabelMap U.object p) /
        gammaMapValue U.form (liftLabelMap U.object p)).val
      rw [div_self']
      change Values.vfValueHom 1 = Values.gammaValHom 1
      rw [map_one,map_one]

end DiamondIntegral.Section6
