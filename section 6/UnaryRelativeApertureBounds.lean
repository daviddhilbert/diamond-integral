import «section 6».UnaryRelativeApertureGeometry
import «section 6».CentripetalBounds

/-! Bounds for the auxiliary unary variable primitive are constructed
from its actual finite endpoint image. No globally named endpoint and
no finite-image RV aperture hypothesis are supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem extendedFocus_inactive (D : UnaryRelativeApertureData A) {p : Mixed M 1 r}
    (hu : p.2 ∉ D.focusData.activeTags.carrier) : D.extendedFocus p=0 :=
  Subtype.ext (scalarExtension_inactive D.focusMap hu)

theorem extendedEndpoint_inactive (D : UnaryRelativeApertureData A) {p : Mixed M 1 r}
    (hu : p.2 ∉ D.focusData.activeTags.carrier) : D.extendedEndpoint p=0 :=
  Subtype.ext (scalarExtension_inactive D.endpointMap hu)

theorem core_inactive (D : UnaryRelativeApertureData A) {p : Mixed M 1 r}
    (hu : p.2 ∉ D.focusData.activeTags.carrier) : D.core p=false := by
  rw [core,D.extendedEndpoint_inactive hu,value_zero]
  exact decide_eq_false (not_lt.mpr (Values.le_infinity _))

theorem point_inactive (D : UnaryRelativeApertureData A) {p : Mixed M 1 r}
    (hu : p.2 ∉ D.focusData.activeTags.carrier) : (D.point p).1=p.1 := by
  simp only [point,D.extendedFocus_inactive hu,D.core_inactive hu,Bool.false_eq_true,
    ite_false,sub_zero,add_zero,Function.update_eq_self]

theorem point_active_bounds (D : UnaryRelativeApertureData A)
    (p : focusActive A D.focusData.activeTags) :
    vfValue (p.val.1 0) ≤ vfValue ((D.point p.val).1 0) ∧
      vfValue ((D.point p.val).1 0) ≤ vfValue (D.endpoint p.val.2) := by
  have hF : vfValue (D.focusData.focus p.val.2)=vfValue (p.val.1 0) :=
    congrArg Values.vrv (D.focusData.focusRV p.val p.property.1 p.property.2)
  by_cases hb : D.core p.val=true
  · have hv := congrArg Values.vrv (D.core_output_RV p hb)
    change vfValue ((D.point p.val).1 0)=vfValue (D.endpoint p.val.2) at hv
    rw [hv]
    exact ⟨hF.symm.trans_le (D.endpoint_nonnegative p),le_rfl⟩
  · have hfalse : D.core p.val=false := Bool.eq_false_iff.mpr hb
    have hle : vfValue (p.val.1 0-D.focusData.focus p.val.2) ≤ vfValue (D.endpoint p.val.2) := by
      have h := hfalse
      rw [D.core_active p] at h
      exact le_of_not_gt (of_decide_eq_false h)
    have hlow := vfValue_min_le_sub (p.val.1 0) (D.focusData.focus p.val.2)
    change min (vfValue (p.val.1 0)) (vfValue (D.focusData.focus p.val.2)) ≤ _ at hlow
    rw [hF,min_self] at hlow
    have hvalue : (D.point p.val).1 0=p.val.1 0-D.focusData.focus p.val.2 := by
      simp only [point,coordinate,Function.update_self,hfalse,Bool.false_eq_true,ite_false,
        add_zero,D.extendedFocus_active p]
    rw [hvalue]
    exact ⟨hlow,hle⟩

theorem endpoint_value_bound (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) :
    ∃ β : Gamma M,∀ p : focusActive A D.focusData.activeTags,vfValue (D.endpoint p.val.2) ≤ β.val := by
  let val (b : VF M) : Gamma M := if hb : b≠0 then finiteValue b hb else 1
  obtain ⟨β,hβ⟩ := ((D.endpointImage_finite hc hs hsmall).image val).bddAbove
  refine ⟨β,fun p => ?_⟩
  have hb : D.endpoint p.val.2 ∈ scalarFocusImage D.endpointMap := ⟨p,D.endpointMap_eq p⟩
  have h := hβ (Set.mem_image_of_mem val hb)
  have he : val (D.endpoint p.val.2)=finiteValue (D.endpoint p.val.2) (D.endpoint_nonzero p) := by
    simp only [val,dif_pos (D.endpoint_nonzero p)]
  rw [he] at h
  exact h

theorem image_vfDoublyBounded (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : VFDoublyBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.focusData.sourceDoublyBounded
  obtain ⟨β,hβ⟩ := D.endpoint_value_bound hc hs hsmall
  let η : Gamma M := max γ β
  have hlow : (η⁻¹).val ≤ (γ⁻¹).val := show η⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  rw [D.image_carrier]
  refine ⟨η,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  fin_cases i
  by_cases hu : p.2 ∈ D.focusData.activeTags.carrier
  · have h := D.point_active_bounds ⟨p,hp,hu⟩
    exact ⟨hlow.trans ((hγ p hp 0).1.trans h.1),h.2.trans ((hβ ⟨p,hp,hu⟩).trans (le_max_right _ _))⟩
  · rw [D.point_inactive hu]
    exact ⟨hlow.trans (hγ p hp 0).1,(hγ p hp 0).2.trans (le_max_left _ _)⟩

theorem image_rvDoublyBounded (D : UnaryRelativeApertureData A) :
    RVSupportDoublyBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.focusData.sourceProper.rvBounded
  let η : Gamma M := max γ 1
  have hlow : (η⁻¹).val ≤ (γ⁻¹).val := show η⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  rw [D.image_carrier]
  refine ⟨η,?_⟩
  rintro _ ⟨p,hp,rfl⟩ i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hOne := branchTag_value (M := M) (D.core p)
    simpa only [point,Fin.append_left,hOne] using
      (show (η⁻¹).val ≤ (1 : GammaInfinity M) ∧ (1 : GammaInfinity M) ≤ η.val from
        ⟨show η⁻¹ ≤ 1 from by simpa only [inv_one] using inv_le_inv' (le_max_right γ 1),le_max_right _ _⟩)
  · simpa only [point,Fin.append_right] using
      (show (η⁻¹).val ≤ Values.vrv (p.2 j) ∧ Values.vrv (p.2 j) ≤ η.val from
        ⟨hlow.trans (hγ p hp j).1,(hγ p hp j).2.trans (le_max_left _ _)⟩)

end DiamondIntegral.Section6.UnaryRelativeApertureData
