import «section 6».CentripetalMap

/-! Finite apertures bound the actual translated VF coordinates on both
branches. The unit branch tags preserve double boundedness of RV support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem focus_value (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    vfValue (D.extendedFocus p) = vfValue (p.1 D.coordinate) := by
  rw [D.extendedFocus_active hp hu]
  exact congrArg Values.vrv (D.focusRV p hp hu)

theorem focus_nonzero (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) : D.extendedFocus p ≠ 0 := by
  intro he
  have hv := D.focus_value hp hu
  rw [he,value_zero] at hv
  exact D.sourceDoublyBounded.nonzero hp D.coordinate ((vfValue_eq_infinity_iff _).mp hv.symm)

theorem core_inactive (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hu : p.2 ∉ D.activeTags.carrier) : D.core p = false := by
  rw [core,D.extendedFocus_inactive hu]
  simp only [mul_zero,value_zero,sub_zero]
  exact decide_eq_false (not_lt.mpr (Values.le_infinity _))

theorem point_inactive (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hu : p.2 ∉ D.activeTags.carrier) : (D.point p).1 = p.1 := by
  classical
  simp only [point,D.extendedFocus_inactive hu,D.core_inactive hu,Bool.false_eq_true,
    ite_false,sub_zero,add_zero,Function.update_eq_self]

theorem core_output_value (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) (hc : D.core p = true) :
    vfValue ((D.point p).1 D.coordinate) = vfValue D.coefficient * vfValue (p.1 D.coordinate) := by
  have hlt : vfValue (D.coefficient * D.extendedFocus p) <
      vfValue (p.1 D.coordinate - D.extendedFocus p) := of_decide_eq_true hc
  have he : rv M ((D.point p).1 D.coordinate) = rv M (D.coefficient * D.extendedFocus p) := by
    apply rv_eq_of_value_close (mul_ne_zero D.coefficient_nonzero (D.focus_nonzero hp hu))
    simpa only [point,Function.update_self,hc,ite_true,add_sub_cancel_right] using hlt
  calc
    vfValue ((D.point p).1 D.coordinate) = vfValue (D.coefficient * D.extendedFocus p) :=
      congrArg Values.vrv he
    _ = vfValue D.coefficient * vfValue (p.1 D.coordinate) := by
      change Values.vfValueHom _ = _
      rw [map_mul]
      change vfValue D.coefficient * vfValue (D.extendedFocus p) = _
      rw [D.focus_value hp hu]

theorem point_coordinate_bounds (D : CentripetalData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) : vfValue (p.1 D.coordinate) ≤ vfValue ((D.point p).1 D.coordinate) ∧
      vfValue ((D.point p).1 D.coordinate) ≤ vfValue D.coefficient * vfValue (p.1 D.coordinate) := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · by_cases hc : D.core p = true
    · rw [D.core_output_value hp hu hc]
      exact ⟨by simpa only [one_mul] using
        mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue (p.1 D.coordinate))),le_rfl⟩
    · have hfalse : D.core p = false := Bool.eq_false_iff.mpr hc
      have hle : vfValue (p.1 D.coordinate - D.extendedFocus p) ≤
          vfValue (D.coefficient * D.extendedFocus p) :=
        le_of_not_gt (of_decide_eq_false hfalse)
      have hlow := vfValue_min_le_sub (p.1 D.coordinate) (D.extendedFocus p)
      change min (vfValue (p.1 D.coordinate)) (vfValue (D.extendedFocus p)) ≤ _ at hlow
      rw [D.focus_value hp hu,min_self] at hlow
      have hprod : vfValue (D.coefficient * D.extendedFocus p) =
          vfValue D.coefficient * vfValue (p.1 D.coordinate) := by
        change Values.vfValueHom _ = _
        rw [map_mul]
        change vfValue D.coefficient * vfValue (D.extendedFocus p) = _
        rw [D.focus_value hp hu]
      simpa only [point,Function.update_self,hfalse,Bool.false_eq_true,ite_false,add_zero,hprod] using
        (show vfValue (p.1 D.coordinate) ≤ vfValue (p.1 D.coordinate - D.extendedFocus p) ∧
          vfValue (p.1 D.coordinate - D.extendedFocus p) ≤
            vfValue D.coefficient * vfValue (p.1 D.coordinate) from ⟨hlow,hle.trans_eq hprod⟩)
  · rw [D.point_inactive hu]
    exact ⟨le_rfl,by
      simpa only [one_mul] using
        mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue (p.1 D.coordinate)))⟩

theorem image_vfDoublyBounded (D : CentripetalData (G := G) A) : VFDoublyBounded D.map.image.carrier := by
  classical
  obtain ⟨γ,hγ⟩ := D.sourceDoublyBounded
  let c := finiteValue D.coefficient D.coefficient_nonzero
  let δ : Gamma M := max γ (c * γ)
  have hlow : (δ⁻¹).val ≤ (γ⁻¹).val := show δ⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hhigh : (c * γ).val ≤ δ.val := le_max_right _ _
  rw [D.image_carrier]
  refine ⟨δ,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  by_cases hi : i = D.coordinate
  · subst i
    have hb := D.point_coordinate_bounds hp
    refine ⟨hlow.trans ((hγ p hp D.coordinate).1.trans hb.1),hb.2.trans ?_⟩
    have hm := mul_le_mul' (le_refl (vfValue D.coefficient)) (hγ p hp D.coordinate).2
    exact hm.trans hhigh
  · have he : (D.point p).1 i = p.1 i := by simp only [point,Function.update_of_ne hi]
    rw [he]
    exact ⟨hlow.trans (hγ p hp i).1,(hγ p hp i).2.trans (show γ.val ≤ δ.val from le_max_left _ _)⟩

theorem image_rvDoublyBounded (D : CentripetalData (G := G) A) :
    RVSupportDoublyBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.sourceProper.rvBounded
  let δ : Gamma M := max 1 γ
  have hlow : (δ⁻¹).val ≤ (γ⁻¹).val := show δ⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_right _ _)
  have hlow1 : (δ⁻¹).val ≤ (1 : GammaInfinity M) :=
    show δ⁻¹ ≤ (1 : Gamma M) from by
      simpa only [inv_one] using inv_le_inv' (show (1 : Gamma M) ≤ δ from le_max_left _ _)
  have hhigh : γ.val ≤ δ.val := le_max_right _ _
  have hhigh1 : (1 : GammaInfinity M) ≤ δ.val := show (1 : Gamma M) ≤ δ from le_max_left _ _
  rw [D.image_carrier]
  refine ⟨δ,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [point,Fin.append_left,branchTag_value] using And.intro hlow1 hhigh1
  · simpa only [point,Fin.append_right] using
      And.intro (hlow.trans (hγ p hp i).1) ((hγ p hp i).2.trans hhigh)

end DiamondIntegral.Section6.CentripetalData
