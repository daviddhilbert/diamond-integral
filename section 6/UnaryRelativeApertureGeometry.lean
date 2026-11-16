import «section 6».UnaryRelativeApertureMap

/-! The auxiliary variable unary primitive has the exact prescribed
core image, including actual source membership of its inverse. It is
locally a translation on each retained branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem focus_nonzero (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) : D.focusData.focus p.val.2≠0 := by
  intro he
  have hr := D.focusData.focusRV p.val p.property.1 p.property.2
  rw [he] at hr
  exact D.focusData.sourceDoublyBounded.nonzero p.property.1 0
    ((SpecialTransformations.Section5.rv_eq_zero_iff _).mp hr.symm)

theorem point_active (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) :
    (D.point p.val).1 0=unaryApertureValue (D.focusData.focus p.val.2) (D.endpoint p.val.2) (p.val.1 0) := by
  have hF := D.extendedFocus_active p
  have hE := D.extendedEndpoint_active p
  simp only [point,coordinate,Function.update_self,core,hF,hE,
    unaryApertureValue,unaryApertureCore]

theorem core_active (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) :
    D.core p.val=unaryApertureCore (D.focusData.focus p.val.2) (D.endpoint p.val.2) (p.val.1 0) := by
  simp only [core,coordinate,D.extendedFocus_active p,D.extendedEndpoint_active p,unaryApertureCore]

theorem core_output_RV (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) (hp : D.core p.val=true) :
    rv M ((D.point p.val).1 0)=rv M (D.endpoint p.val.2) := by
  have hcore := hp
  rw [D.core_active p] at hcore
  rw [D.point_active p]
  apply (rv_eq_iff_value_close (D.endpoint_nonzero p)).mpr
  simpa only [unaryApertureValue,hcore,ite_true,add_sub_cancel_right] using
    (of_decide_eq_true hcore)

theorem core_source_saturated (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) (hp : D.core p.val=true)
    (z : VF M) (hz : vfValue (D.endpoint p.val.2)<vfValue (z-D.focusData.focus p.val.2)) :
    ((fun _ : Fin 1 => z),p.val.2) ∈ A.carrier := by
  have hpc : vfValue (D.endpoint p.val.2)<vfValue (p.val.1 0-D.focusData.focus p.val.2) := by
    have h := hp
    rw [D.core_active p] at h
    exact of_decide_eq_true h
  have hclose : (D.radius p.val.2).val<vfValue (p.val.1 0-z) := by
    have hmin := vfValue_min_le_sub (p.val.1 0-D.focusData.focus p.val.2)
      (z-D.focusData.focus p.val.2)
    rw [show p.val.1 0-D.focusData.focus p.val.2-(z-D.focusData.focus p.val.2)=p.val.1 0-z by abel] at hmin
    exact (D.radius_le_endpoint p).trans_lt ((lt_min hpc hz).trans_le hmin)
  apply (D.invariant p.val.2 p.val.1 (fun _ => z) ?_).mp p.property.1
  intro i
  fin_cases i
  exact hclose

theorem core_image_full_RV_disc (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) (hp : D.core p.val=true)
    (y : VF M) (hy : rv M y=rv M (D.endpoint p.val.2)) :
    ∃ q : focusActive A D.focusData.activeTags,q.val.2=p.val.2 ∧
      D.core q.val=true ∧ (D.point q.val).1 0=y := by
  obtain ⟨z,⟨hzRV,hzCore⟩,hzy⟩ :=
    (Set.ext_iff.mp (unary_core_image (D.focusData.focus p.val.2) (D.endpoint p.val.2)
      (D.focus_nonzero p) (D.endpoint_nonzero p) (D.endpoint_nonnegative p)) y).mpr hy
  have hzA := D.core_source_saturated p hp z hzCore
  let q : focusActive A D.focusData.activeTags := ⟨((fun _ => z),p.val.2),hzA,p.property.2⟩
  have hq : D.core q.val=true := by
    rw [D.core_active q]
    exact decide_eq_true hzCore
  refine ⟨q,rfl,hq,?_⟩
  rw [D.point_active q]
  have hqc := hq
  rw [D.core_active q] at hqc
  simpa only [unaryApertureValue,hqc,ite_true] using hzy

theorem branch_translation (D : UnaryRelativeApertureData A)
    {p q : Mixed M 1 r} (hp : p ∈ A.carrier) (hq : q ∈ A.carrier)
    (hu : p.2=q.2) (hcore : D.core p=D.core q) :
    (D.point p).1 0-(D.point q).1 0=p.1 0-q.1 0 := by
  have hF := D.extendedFocus_same_tags hp hq hu
  have hE := D.extendedEndpoint_same_tags hp hq hu
  simp only [point,coordinate,Function.update_self,hF,hE,hcore]
  abel

end DiamondIntegral.Section6.UnaryRelativeApertureData
