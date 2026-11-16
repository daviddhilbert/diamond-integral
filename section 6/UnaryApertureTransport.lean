import «section 6».UnaryApertureGeometry

/-! Replacing the output of a unary finite-aperture map by any point
with the same leading term lifts within the same input RV disc and the
same retained core branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def unaryApertureCore (a b x : VF M) : Bool := decide (vfValue b < vfValue (x-a))

def unaryApertureValue (a b x : VF M) : VF M := x-a+if unaryApertureCore a b x then b else 0

theorem unaryAperture_transport (a b x y : VF M) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : vfValue a ≤ vfValue b) (hx : rv M x = rv M a)
    (hy : rv M y = rv M (unaryApertureValue a b x)) :
    ∃ z : VF M, rv M z = rv M x ∧ unaryApertureCore a b z = unaryApertureCore a b x ∧
      unaryApertureValue a b z = y := by
  by_cases hc : unaryApertureCore a b x = true
  · have hcut : vfValue b < vfValue (x-a) := of_decide_eq_true hc
    have hxy : unaryApertureValue a b x = x-a+b := by simp only [unaryApertureValue,hc,ite_true]
    have hyb : rv M y = rv M b := hy.trans (by
      rw [hxy]
      apply (rv_eq_iff_value_close hb).mpr
      simpa only [add_sub_cancel_right] using hcut)
    obtain ⟨z,⟨hz,hzcut⟩,hzy⟩ := Set.ext_iff.mp (unary_core_image a b ha hb hab) y |>.mpr hyb
    have hzcore : unaryApertureCore a b z = true := decide_eq_true hzcut
    exact ⟨z,hz.trans hx.symm,hzcore.trans hc.symm,by
      simpa only [unaryApertureValue,hzcore,ite_true] using hzy⟩
  · have hcf : unaryApertureCore a b x = false := Bool.eq_false_iff.mpr hc
    have hcut : vfValue (x-a) ≤ vfValue b := le_of_not_gt (of_decide_eq_false hcf)
    have hxy : unaryApertureValue a b x = x-a := by
      simp only [unaryApertureValue,hcf,Bool.false_eq_true,ite_false,add_zero]
    let ρ := finiteValue b hb
    have hvalue : vfValue y = vfValue (x-a) := by
      change Values.vrv (rv M y) = Values.vrv (rv M (x-a))
      rw [← hxy]
      exact congrArg Values.vrv hy
    have hyset : y ∈ {y | vfValue a < vfValue y ∧ vfValue y ≤ ρ.val} :=
      ⟨((rv_eq_iff_value_close ha).mp hx).trans_eq hvalue.symm,hvalue.le.trans hcut⟩
    obtain ⟨z,⟨hz,hzcut⟩,hzy⟩ := Set.ext_iff.mp (unary_noncore_image a ha ρ) y |>.mpr hyset
    have hzcore : unaryApertureCore a b z = false := decide_eq_false (not_lt.mpr hzcut)
    exact ⟨z,hz.trans hx.symm,hzcore.trans hcf.symm,by
      simpa only [unaryApertureValue,hzcore,Bool.false_eq_true,ite_false,add_zero] using hzy⟩

end DiamondIntegral.Section6
