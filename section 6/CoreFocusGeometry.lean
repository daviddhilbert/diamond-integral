import «section 6».CoreCoordinateBundles

/-! The focus graph is an actual source point on an RV-pullback.
It lies in the actual core, whose output leading term is the named
coefficient times the focus leading term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_point_rv (D : CentripetalData (G := G) A) (a : Mixed M n r)
    (ha : a ∈ A.carrier) (hCore : D.core a = true) :
    rv M ((D.point a).1 D.coordinate) = rv M (D.coefficient*D.extendedFocus a) := by
  have hf0 := D.focus_nonzero ha (D.core_true_active a hCore)
  apply (rv_eq_iff_value_close (mul_ne_zero D.coefficient_nonzero hf0)).mpr
  simpa only [point,Function.update_self,hCore,ite_true,add_sub_cancel_right] using
    (show vfValue (D.coefficient*D.extendedFocus a) <
      vfValue (a.1 D.coordinate-D.extendedFocus a) from of_decide_eq_true hCore)

theorem focusPoint_extendedFocus (D : CentripetalData (G := G) A) (a : Mixed M n r)
    (ha : a ∈ A.carrier) (hGraph : D.focusPoint a ∈ A.carrier) :
    D.extendedFocus (D.focusPoint a) = D.extendedFocus a := by
  exact (D.extendedFocus_same_other ha hGraph rfl (fun i hi => by
    simp only [focusPoint,Function.update_of_ne hi])).symm

theorem focusPoint_core (D : CentripetalData (G := G) A) (a : Mixed M n r)
    (ha : a ∈ A.carrier) (hu : a.2 ∈ D.activeTags.carrier)
    (hGraph : D.focusPoint a ∈ A.carrier) : D.core (D.focusPoint a) = true := by
  have hFocus := D.extendedFocus_active ha hu
  apply decide_eq_true_eq.mpr
  rw [D.focusPoint_extendedFocus a ha hGraph]
  simp only [focusPoint,Function.update_self,← hFocus,sub_self]
  exact gamma_lt_value_zero (finiteValue (D.coefficient*D.extendedFocus a)
    (mul_ne_zero D.coefficient_nonzero (D.focus_nonzero ha hu)))

end DiamondIntegral.Section6.CentripetalData
