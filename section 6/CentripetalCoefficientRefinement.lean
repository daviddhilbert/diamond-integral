import «section 6».PullbackLocusExtension

/-! Increasing a named coefficient's valuation gives an actual permitted
finite-aperture component. Its core shrinks, and both actual maps agree
on the old noncore branch. -/

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

def refineCoefficient (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) : CentripetalData (G := G) A where
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
  coefficient := c
  coefficient_nonzero := hc0
  coefficient_nonnegative := D.coefficient_nonnegative.trans hval
  coefficient_definable := hcdef
  covariance := by
    intro u hu
    obtain ⟨α,β,hα,hβ,hInv,hcov,hdom⟩ := D.covariance u hu
    refine ⟨α,β,hα,hβ,hInv,hcov,fun a ha => (hdom a ha).trans ?_⟩
    change Values.vfValueHom (D.coefficient * _) ≤ Values.vfValueHom (c * _)
    rw [map_mul,map_mul]
    exact mul_le_mul' hval le_rfl

theorem refineCoefficient_extendedFocus (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) (p : Mixed M n r) :
    (D.refineCoefficient c hc0 hcdef hval).extendedFocus p = D.extendedFocus p := rfl

theorem refineCoefficient_core_subset (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) (p : Mixed M n r)
    (hp : (D.refineCoefficient c hc0 hcdef hval).core p = true) : D.core p = true := by
  have hcut : vfValue (D.coefficient * D.extendedFocus p) ≤ vfValue (c * D.extendedFocus p) := by
    change Values.vfValueHom (D.coefficient * _) ≤ Values.vfValueHom (c * _)
    rw [map_mul,map_mul]
    exact mul_le_mul' hval le_rfl
  apply decide_eq_true_eq.mpr
  exact hcut.trans_lt (decide_eq_true_eq.mp hp)

theorem refineCoefficient_noncore_agrees (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) (p : Mixed M n r) (hp : D.core p = false) :
    (D.refineCoefficient c hc0 hcdef hval).point p = D.point p := by
  have hnew : (D.refineCoefficient c hc0 hcdef hval).core p = false := by
    apply Bool.eq_false_iff.mpr
    intro hn
    exact Bool.noConfusion (hp.symm.trans (D.refineCoefficient_core_subset c hc0 hcdef hval p hn))
  simp only [point,hnew,hp,Bool.false_eq_true,ite_false,add_zero,refineCoefficient_extendedFocus]
  rfl

theorem refineCoefficient_released_iff (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) (p : Mixed M n r) :
    (D.core p = true ∧ (D.refineCoefficient c hc0 hcdef hval).core p = false) ↔
      vfValue (D.coefficient * D.extendedFocus p) < vfValue (p.1 D.coordinate - D.extendedFocus p) ∧
        vfValue (p.1 D.coordinate - D.extendedFocus p) ≤ vfValue (c * D.extendedFocus p) := by
  simp only [core,decide_eq_true_eq,decide_eq_false_iff_not,not_lt]
  rfl

end DiamondIntegral.Section6.CentripetalData
