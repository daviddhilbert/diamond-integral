import «section 6».ReleasedBranchDomains

/-! On the actual annulus released by coefficient refinement, every
replacement with the same leading term comes from the actual source.
The refined component leaves that replacement on its noncore branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_true_active (D : CentripetalData (G := G) A) (p : Mixed M n r)
    (hp : D.core p = true) : p.2 ∈ D.activeTags.carrier := by
  by_contra hn
  exact Bool.noConfusion ((D.core_inactive hn).symm.trans hp)

theorem released_coordinate_replacement
    (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c)
    (a : Mixed M n r) (ha : a ∈ (D.releasedDomain (D.refineCoefficient c hc0 hcdef hval)).carrier)
    (d : VF M) (hrv : rv M d = rv M (((D.refineCoefficient c hc0 hcdef hval).point a).1 D.coordinate)) :
    ∃ b, b ∈ (D.releasedDomain (D.refineCoefficient c hc0 hcdef hval)).carrier ∧
      (D.refineCoefficient c hc0 hcdef hval).point b =
        (Function.update ((D.refineCoefficient c hc0 hcdef hval).point a).1 D.coordinate d,
          ((D.refineCoefficient c hc0 hcdef hval).point a).2) := by
  let E := D.refineCoefficient c hc0 hcdef hval
  have hcoord : E.coordinate = D.coordinate := rfl
  have hCoeff : E.coefficient = c := rfl
  have hEA : E.core a = false := ha.2.2
  let focus := D.focus (Function.update a.1 D.coordinate 0) a.2
  let b : Mixed M n r := (Function.update a.1 D.coordinate (d+focus),a.2)
  have hu : a.2 ∈ D.activeTags.carrier := D.core_true_active a ha.2.1
  have hFocus : D.extendedFocus a = focus := D.extendedFocus_active ha.1 hu
  have hEFocus : E.extendedFocus a = focus := hFocus
  have hValue : vfValue d = vfValue (a.1 D.coordinate-focus) := by
    have he : ((E.point a).1 D.coordinate) = a.1 D.coordinate-focus := by
      simp only [point,hcoord,Function.update_self,hEA,Bool.false_eq_true,ite_false,add_zero,hEFocus]
    have hh := congrArg Values.vrv hrv
    change vfValue d = vfValue ((E.point a).1 D.coordinate) at hh
    exact hh.trans (congrArg vfValue he)
  have hErase : Function.update b.1 D.coordinate 0 = Function.update a.1 D.coordinate 0 := by
    simp only [b,Function.update_idem]
  have hbFocus : D.focus (Function.update b.1 D.coordinate 0) b.2 = focus := by rw [hErase]
  have hFocusPoint : D.focusPoint b = D.focusPoint a := by
    simp only [focusPoint,hbFocus,b,Function.update_idem]
  have hOld : vfValue (D.coefficient*focus) < vfValue (a.1 D.coordinate-focus) := by
    have hh := decide_eq_true_eq.mp ha.2.1
    simpa only [core,hFocus] using hh
  have hNew : vfValue (a.1 D.coordinate-focus) ≤ vfValue (c*focus) := by
    have hh := decide_eq_false_iff_not.mp hEA
    simpa only [hcoord,hCoeff,hEFocus,not_lt] using hh
  have hBclose : vfValue (D.coefficient * D.focus (Function.update b.1 D.coordinate 0) b.2) <
      vfValue (b.1 D.coordinate - D.focus (Function.update b.1 D.coordinate 0) b.2) := by
    simpa only [hbFocus,b,Function.update_self,add_sub_cancel_right,hValue] using hOld
  have hFocusMem : D.focusPoint a ∈ A.carrier :=
    (D.core_membership_iff_focus a hu (by simpa only [focus] using hOld)).mp ha.1
  have hbA : b ∈ A.carrier := (D.core_membership_iff_focus b hu hBclose).mpr
    (hFocusPoint.symm ▸ hFocusMem)
  have hBF : D.extendedFocus b = focus := (D.extendedFocus_active hbA hu).trans hbFocus
  have hBEF : E.extendedFocus b = focus := hBF
  have hbOld : D.core b = true := by
    apply decide_eq_true_eq.mpr
    simpa only [hBF,b,Function.update_self,add_sub_cancel_right,hValue] using hOld
  have hbNew : E.core b = false := by
    apply decide_eq_false_iff_not.mpr
    apply not_lt.mpr
    simpa only [hcoord,hCoeff,hBEF,b,Function.update_self,add_sub_cancel_right,hValue] using hNew
  refine ⟨b,⟨hbA,hbOld,hbNew⟩,?_⟩
  change E.point b = (Function.update (E.point a).1 D.coordinate d,(E.point a).2)
  apply Prod.ext
  · simp only [point,hcoord,hbNew,hEA,Bool.false_eq_true,ite_false,add_zero,hBEF,hEFocus,
      b,Function.update_self,add_sub_cancel_right,Function.update_idem]
  · simp only [point,hbNew,hEA,b]

end DiamondIntegral.Section6.CentripetalData
