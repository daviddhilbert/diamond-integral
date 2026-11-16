import «section 6».ApertureCore

/-! Exact images of the two unary finite-aperture clauses. Both images
are unions of complete RV discs. These are full field-set equalities,
not merely equalities of their leading-term projections. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unary_noncore_image (a : VF M) (ha : a ≠ 0) (ρ : Gamma M) :
    (fun x : VF M => x-a) '' {x | rv M x = rv M a ∧ vfValue (x-a) ≤ ρ.val} =
      {y | vfValue a < vfValue y ∧ vfValue y ≤ ρ.val} := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hcut⟩,rfl⟩
    exact ⟨(rv_eq_iff_value_close ha).mp hx,hcut⟩
  · rintro ⟨hnear,hcut⟩
    refine ⟨y+a,⟨(rv_eq_iff_value_close ha).mpr ?_,?_⟩,add_sub_cancel_right _ _⟩
    · simpa only [add_sub_cancel_right] using hnear
    · simpa only [add_sub_cancel_right] using hcut

theorem unary_core_image (a b : VF M) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : vfValue a ≤ vfValue b) :
    (fun x : VF M => x-a+b) '' {x | rv M x = rv M a ∧ vfValue b < vfValue (x-a)} =
      {y | rv M y = rv M b} := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hcut⟩,rfl⟩
    apply (rv_eq_iff_value_close hb).mpr
    simpa only [add_sub_cancel_right] using hcut
  · intro hy
    have hcut := (rv_eq_iff_value_close hb).mp hy
    refine ⟨y-b+a,⟨(rv_eq_iff_value_close ha).mpr ?_,?_⟩,?_⟩
    · simpa only [add_sub_cancel_right] using hab.trans_lt hcut
    · simpa only [add_sub_cancel_right] using hcut
    · abel

def UnaryApertureImage (a b : VF M) (ρ : Gamma M) (core : Bool) : Set (VF M) :=
  if core then {y | rv M y = rv M b} else {y | vfValue a < vfValue y ∧ vfValue y ≤ ρ.val}

theorem unaryApertureImage_rv_saturated (a b : VF M) (ρ : Gamma M) (core : Bool)
    (x y : VF M) (hxy : rv M x = rv M y) :
    x ∈ UnaryApertureImage a b ρ core ↔ y ∈ UnaryApertureImage a b ρ core := by
  have hv : vfValue x = vfValue y := congrArg Values.vrv hxy
  cases core <;> simp only [UnaryApertureImage,Bool.false_eq_true,ite_false,ite_true,Set.mem_ofPred_eq]
  · rw [hv]
  · rw [hxy]

theorem unaryApertureImage_nonzero (a b : VF M) (ha : a ≠ 0) (hb : b ≠ 0)
    (ρ : Gamma M) (core : Bool) {x : VF M} (hx : x ∈ UnaryApertureImage a b ρ core) : x ≠ 0 := by
  cases core
  · have hbound : vfValue x ≤ ρ.val := hx.2
    intro he
    rw [he,value_zero] at hbound
    exact ρ.property (le_antisymm (Values.le_infinity _) hbound)
  · intro he
    have hrv : rv M (0 : VF M) = rv M b := he ▸ hx
    have hv := (rv_eq_iff_value_close hb).mp hrv
    rw [zero_sub] at hv
    change vfValue b < Values.vfValueHom (-b) at hv
    rw [vfValue_neg,valueHom_eq_value] at hv
    exact lt_irrefl _ hv

end DiamondIntegral.Section6
