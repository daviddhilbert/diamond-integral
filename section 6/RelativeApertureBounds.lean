import «section 6».RelativeApertureMap
import «section 6».CentripetalBounds

/-! Uniform bounds for the arbitrary-arity variable primitive use the
actual relative valuation bound, not finiteness of its VF endpoint image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem focus_value (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    vfValue (D.extendedFocus p) = vfValue (p.1 D.coordinate) := by
  rw [D.extendedFocus_active hp hu]
  exact congrArg Values.vrv (D.focusRV p hp hu)

theorem focus_nonzero (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) : D.extendedFocus p ≠ 0 := by
  intro he
  have hv := D.focus_value hp hu
  rw [he,value_zero] at hv
  exact D.sourceDoublyBounded.nonzero hp D.coordinate ((vfValue_eq_infinity_iff _).mp hv.symm)

theorem endpoint_nonzero_at (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) : D.extendedEndpoint p≠0 := by
  rw [D.extendedEndpoint_active hp hu]
  exact D.endpoint_nonzero ⟨p,hp,hu⟩

theorem endpoint_lower (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    vfValue (p.1 D.coordinate) ≤ vfValue (D.extendedEndpoint p) := by
  rw [← D.focus_value hp hu,D.extendedFocus_active hp hu,D.extendedEndpoint_active hp hu]
  exact D.endpoint_nonnegative ⟨p,hp,hu⟩

theorem endpoint_upper (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    vfValue (D.extendedEndpoint p) ≤ D.apertureBound.val*vfValue (p.1 D.coordinate) := by
  rw [D.extendedEndpoint_active hp hu,← D.endpointMap_eq ⟨p,hp,hu⟩]
  exact D.endpoint_upper_bound ⟨p,hp,hu⟩

theorem core_inactive (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hu : p.2 ∉ D.activeTags.carrier) : D.core p=false := by
  rw [core,D.extendedEndpoint_inactive hu,value_zero]
  exact decide_eq_false (not_lt.mpr (Values.le_infinity _))

theorem point_inactive (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hu : p.2 ∉ D.activeTags.carrier) : (D.point p).1=p.1 := by
  classical
  simp only [point,D.extendedFocus_inactive hu,D.core_inactive hu,Bool.false_eq_true,
    ite_false,sub_zero,add_zero,Function.update_eq_self]

theorem core_output_RV (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) (hb : D.core p=true) :
    rv M ((D.point p).1 D.coordinate)=rv M (D.extendedEndpoint p) := by
  apply rv_eq_of_value_close (D.endpoint_nonzero_at hp hu)
  simpa only [point,Function.update_self,hb,ite_true,add_sub_cancel_right] using of_decide_eq_true hb

theorem point_coordinate_bounds (D : RelativeApertureData (G := G) A) {p : Mixed M n r}
    (hp : p ∈ A.carrier) : vfValue (p.1 D.coordinate) ≤ vfValue ((D.point p).1 D.coordinate) ∧
      vfValue ((D.point p).1 D.coordinate) ≤ D.apertureBound.val*vfValue (p.1 D.coordinate) := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · by_cases hb : D.core p=true
    · have he : vfValue ((D.point p).1 D.coordinate)=vfValue (D.extendedEndpoint p) :=
        congrArg Values.vrv (D.core_output_RV hp hu hb)
      rw [he]
      exact ⟨D.endpoint_lower hp hu,D.endpoint_upper hp hu⟩
    · have hfalse : D.core p=false := Bool.eq_false_iff.mpr hb
      have hle : vfValue (p.1 D.coordinate-D.extendedFocus p) ≤ vfValue (D.extendedEndpoint p) :=
        le_of_not_gt (of_decide_eq_false hfalse)
      have hlow := vfValue_min_le_sub (p.1 D.coordinate) (D.extendedFocus p)
      change min (vfValue (p.1 D.coordinate)) (vfValue (D.extendedFocus p)) ≤ _ at hlow
      rw [D.focus_value hp hu,min_self] at hlow
      have hlow' : vfValue (p.1 D.coordinate) ≤ vfValue (p.1 D.coordinate-D.extendedFocus p) := hlow
      simp only [point,Function.update_self,hfalse,Bool.false_eq_true,ite_false,add_zero]
      exact ⟨hlow',hle.trans (D.endpoint_upper hp hu)⟩
  · rw [D.point_inactive hu]
    refine ⟨le_rfl,?_⟩
    have hDelta : (1 : GammaInfinity M) ≤ D.apertureBound.val := D.apertureBound_nonnegative
    simpa only [one_mul] using (mul_le_mul' hDelta (le_refl (vfValue (p.1 D.coordinate))))

theorem image_vfDoublyBounded (D : RelativeApertureData (G := G) A) : VFDoublyBounded D.map.image.carrier := by
  classical
  obtain ⟨γ,hγ⟩ := D.sourceDoublyBounded
  let c := D.apertureBound
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
    have hm := mul_le_mul' (le_refl (D.apertureBound.val)) (hγ p hp D.coordinate).2
    exact hm.trans hhigh
  · have he : (D.point p).1 i = p.1 i := by simp only [point,Function.update_of_ne hi]
    rw [he]
    exact ⟨hlow.trans (hγ p hp i).1,(hγ p hp i).2.trans (show γ.val ≤ δ.val from le_max_left _ _)⟩

theorem image_rvDoublyBounded (D : RelativeApertureData (G := G) A) :
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

end DiamondIntegral.Section6.RelativeApertureData
