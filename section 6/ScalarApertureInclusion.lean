import «section 6».RelativeApertureRVGraphs
import «section 6».FocusCutoffValueMaps
import «section 6».NamedVFValues

/-! Every original scalar primitive is actual admissible variable data.
Its complete VF map and branch tags agree, so old Section 6 witnesses
remain literal witnesses after the proposed enlargement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def relativeData (D : CentripetalData (G := G) A) : RelativeApertureData (G := G) A where
  coordinate := D.coordinate
  activeTags := D.activeTags
  focus := D.focus
  focusMap := D.focusMap
  focusMap_eq := D.focusMap_eq
  sourceProper := D.sourceProper
  sourceDoublyBounded := D.sourceDoublyBounded
  tagged := D.tagged
  continuous := D.continuous
  focusRV := D.focusRV
  endpoint := fun x u => D.coefficient*D.focus x u
  endpointMap := scalarFocusProductMap D.focusMap D.coefficient D.coefficient_definable
  endpointMap_eq p := by
    rw [scalarFocusProductMap_at,D.focusMap_eq]
  endpoint_continuous u hu := (D.continuous u hu).const_mul D.coefficient
  endpoint_nonzero p := mul_ne_zero D.coefficient_nonzero (by
    have h := D.focus_nonzero p.property.1 p.property.2
    rwa [D.extendedFocus_active p.property.1 p.property.2] at h)
  endpoint_nonnegative p := by
    change vfValue _ ≤ Values.vfValueHom _
    rw [map_mul]
    simpa only [one_mul,valueHom_eq_value] using
      (mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue (D.focus (Function.update p.val.1 D.coordinate 0) p.val.2))))
  endpoint_RV_constant p q he := by
    rw [scalarFocusProductMap_at,scalarFocusProductMap_at]
    have hMul (x y : VF M) : rv M (x*y)=rv M x*rv M y := by
      apply Subtype.ext
      exact (rv_mul_hom_of_model hM x.property y.property).trans (RVOperations.mul_val (rv M x) (rv M y)).symm
    rw [hMul,hMul]
    apply congrArg (fun t => rv M D.coefficient*t)
    rw [D.focusMap_eq,D.focusMap_eq]
    exact (D.focusRV p.val p.property.1 p.property.2).trans
      ((congrFun (D.tagged p.val p.property.1 q.val q.property.1 he) D.coordinate).trans
        (D.focusRV q.val q.property.1 q.property.2).symm)
  apertureBound := finiteValue D.coefficient D.coefficient_nonzero
  apertureBound_nonnegative := D.coefficient_nonnegative
  apertureBound_named := finiteValue_named D.coefficient D.coefficient_nonzero D.coefficient_definable
  endpoint_upper_bound p := by
    rw [scalarFocusProductMap_at]
    change Values.vfValueHom _ ≤ vfValue D.coefficient*vfValue (p.val.1 D.coordinate)
    rw [map_mul]
    have hF : Values.vfValueHom ((D.focusMap p).val 0)=vfValue (p.val.1 D.coordinate) := by
      rw [D.focusMap_eq]
      exact congrArg Values.vrv (D.focusRV p.val p.property.1 p.property.2)
    rw [hF,valueHom_eq_value]
  covariance := D.covariance

theorem relativeData_endpoint (D : CentripetalData (G := G) A) (p : A) :
    D.relativeData.extendedEndpoint p.val=D.coefficient*D.extendedFocus p.val := by
  by_cases hu : p.val.2 ∈ D.activeTags.carrier
  · rw [RelativeApertureData.extendedEndpoint_active D.relativeData p.property hu,
      D.extendedFocus_active p.property hu]
    rfl
  · rw [RelativeApertureData.extendedEndpoint_inactive D.relativeData hu,D.extendedFocus_inactive hu,mul_zero]

theorem relativeData_core (D : CentripetalData (G := G) A) (p : A) : D.relativeData.core p.val=D.core p.val := by
  change decide (vfValue (D.relativeData.extendedEndpoint p.val)<
    vfValue (p.val.1 D.coordinate-D.extendedFocus p.val))=D.core p.val
  rw [D.relativeData_endpoint p]
  rfl

theorem relativeData_point (D : CentripetalData (G := G) A) (p : A) : D.relativeData.point p.val=D.point p.val := by
  change (Function.update p.val.1 D.coordinate (p.val.1 D.coordinate-D.extendedFocus p.val+
      if D.relativeData.core p.val then D.relativeData.extendedEndpoint p.val else 0),
    Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.relativeData.core p.val)) p.val.2)=D.point p.val
  rw [D.relativeData_core p,D.relativeData_endpoint p]
  rfl

end DiamondIntegral.Section6.CentripetalData
