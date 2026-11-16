import «section 6».SpecialCovariantRestrictions
import «section 6».ApertureCore

/-! The core of an actual permitted centripetal map is a complete RV
disc in its changing coordinate. The source need only be invariant at
the aperture radius; it need not already be an RV-pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_image_saturated (D : CentripetalData (G := G) A)
    {a : Mixed M n r} (ha : a ∈ A.carrier) (hcore : D.core a = true)
    (y : VF M) (hy : rv M y = rv M ((D.point a).1 D.coordinate)) :
    (Function.update (D.point a).1 D.coordinate y,(D.point a).2) ∈ D.map.image.carrier := by
  have hu : a.2 ∈ D.activeTags.carrier := by
    by_contra hn
    have hh := D.core_inactive hn
    rw [hcore] at hh
    cases hh
  let focusVal := D.extendedFocus a
  let center := D.coefficient*focusVal
  have hf0 : focusVal ≠ 0 := D.focus_nonzero ha hu
  have hc0 : center ≠ 0 := mul_ne_zero D.coefficient_nonzero hf0
  have hcut : vfValue center < vfValue (a.1 D.coordinate-focusVal) := of_decide_eq_true hcore
  have hrva : rv M ((D.point a).1 D.coordinate) = rv M center := by
    apply (rv_eq_iff_value_close hc0).mpr
    simpa only [point,Function.update_self,hcore,ite_true,add_sub_cancel_right,focusVal,center] using hcut
  have hycut : vfValue center < vfValue (y-center) := (rv_eq_iff_value_close hc0).mp (hy.trans hrva)
  let b : Mixed M n r := (Function.update a.1 D.coordinate (focusVal+(y-center)),a.2)
  obtain ⟨α,β,hα,hβ,hInv,hcov,hdom⟩ := D.covariance a.2 hu
  have hαc : α.val ≤ vfValue center := by
    change α.val ≤ vfValue (D.coefficient*D.extendedFocus a)
    rw [D.extendedFocus_active ha hu]
    exact hdom a.1 ha
  have hcong : Congruent (fun i => if i = D.coordinate then α else β i) a.1 b.1 := by
    intro i
    by_cases hi : i = D.coordinate
    · subst i
      simp only [ite_true,b,Function.update_self]
      have hmin := vfValue_min_le_sub (a.1 D.coordinate-focusVal) (y-center)
      rw [show (a.1 D.coordinate-focusVal)-(y-center) =
        a.1 D.coordinate-(focusVal+(y-center)) by abel] at hmin
      exact hαc.trans_lt ((lt_min hcut hycut).trans_le hmin)
    · simpa only [hi,ite_false,b,Function.update_of_ne hi,sub_self,valueHom_eq_value] using
        gamma_lt_value_zero (β i)
  have hb : b ∈ A.carrier := (hInv a.1 b.1 hcong).mp ha
  have hfocus : D.extendedFocus b = focusVal :=
    (D.extendedFocus_same_other ha hb rfl (fun i hi => by simp only [b,Function.update_of_ne hi])).symm
  have hbcut : vfValue (D.coefficient*D.extendedFocus b) < vfValue (b.1 D.coordinate-D.extendedFocus b) := by
    rw [hfocus]
    simpa only [b,Function.update_self,add_sub_cancel_left,center] using hycut
  have hbcore : D.core b = true := decide_eq_true hbcut
  rw [D.image_carrier]
  refine ⟨b,hb,Prod.ext ?_ ?_⟩
  · funext i
    by_cases hi : i = D.coordinate
    · subst i
      simp only [point,Function.update_self,hbcore,ite_true,hfocus,b]
      change focusVal+(y-center)-focusVal+center = y
      abel
    · simp only [point,Function.update_of_ne hi,b]
  · simp only [point,hbcore,hcore,b]

end DiamondIntegral.Section6.CentripetalData
