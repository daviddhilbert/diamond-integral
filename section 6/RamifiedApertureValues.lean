import «section 6».NamedUnaryOffsets

/-! A scope check for direct paired-aperture replacement. In a cyclic
named value group, a ramified focus and a unit focus cannot have equal
relative-aperture radii with two named coefficients. This is not a
nonexistence assertion about arbitrary complete matching preparations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ramified_relative_aperture_values_ne (ρ γ : Gamma M) (hρ : 1 < ρ) (hγ : γ^2=ρ)
    (m n : ℤ) : ρ^m*γ ≠ ρ^n := by
  intro he
  have hPow : ρ^(m*2+1)=ρ^(n*2) := by
    calc
      ρ^(m*2+1)=(ρ^m*γ)^2 := by simp only [zpow_add,zpow_mul,zpow_ofNat,pow_one,mul_pow,hγ]
      _=(ρ^n)^2 := congrArg (fun x : Gamma M => x^2) he
      _=ρ^(n*2) := by simp only [zpow_mul,zpow_ofNat]
  have hExp := (zpow_right_inj hρ).mp hPow
  omega

theorem ramified_focus_aperture_values_ne (ρ γ : Gamma M) (hρ : 1 < ρ) (hγ : γ^2=ρ)
    (a b c d : VF M) (m n : ℤ)
    (ha : vfValue a=γ.val) (hb : vfValue b=(1 : Gamma M).val)
    (hc : vfValue c=(ρ^m).val) (hd : vfValue d=(ρ^n).val) :
    vfValue (c*a) ≠ vfValue (d*b) := by
  intro he
  have hLeft : vfValue (c*a)=(ρ^m*γ).val := by
    change Values.vfValueHom (c*a)=_
    rw [map_mul,valueHom_eq_value,valueHom_eq_value,hc,ha]
    rfl
  have hRight : vfValue (d*b)=(ρ^n).val := by
    change Values.vfValueHom (d*b)=_
    rw [map_mul,valueHom_eq_value,valueHom_eq_value,hd,hb]
    exact mul_one _
  exact ramified_relative_aperture_values_ne ρ γ hρ hγ m n
    (Subtype.ext (hLeft.symm.trans (he.trans hRight)))

end DiamondIntegral.Section6
