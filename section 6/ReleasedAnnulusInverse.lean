import «section 6».ReleasedPartitionImages

/-! Construct an actual source point for every value in the released
annulus over a focus graph. An RV-pullback ambient supplies that graph
point directly from the permitted focus condition. -/

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

theorem focusPoint_mem_of_rvPullback (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) (a : Mixed M n r) (ha : a ∈ A.carrier)
    (hu : a.2 ∈ D.activeTags.carrier) : D.focusPoint a ∈ A.carrier := by
  apply rvPullback_mem_of_sameRV (q := D.focusPoint a) hA ha ?_ rfl
  funext i
  by_cases hi : i = D.coordinate
  · subst i
    change rv M (a.1 D.coordinate) = rv M ((D.focusPoint a).1 D.coordinate)
    simpa only [focusPoint,Function.update_self] using (D.focusRV a ha hu).symm
  · change rv M (a.1 i) = rv M ((D.focusPoint a).1 i)
    simp only [focusPoint,Function.update_of_ne hi]

theorem released_annulus_inverse
    (D : CentripetalData (G := G) A) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c)
    (a : Mixed M n r) (ha : a ∈ A.carrier) (hu : a.2 ∈ D.activeTags.carrier)
    (hGraph : D.focusPoint a ∈ A.carrier) (d : VF M)
    (hOld : vfValue (D.coefficient * D.extendedFocus a) < vfValue d)
    (hNew : vfValue d ≤ vfValue (c * D.extendedFocus a)) :
    ∃ b, b ∈ (D.releasedDomain (D.refineCoefficient c hc0 hcdef hval)).carrier ∧
      (D.refineCoefficient c hc0 hcdef hval).point b =
        (Function.update a.1 D.coordinate d,
          Fin.append (fun _ : Fin 1 => branchTag (M := M) false) a.2) := by
  let E := D.refineCoefficient c hc0 hcdef hval
  let focus := D.focus (Function.update a.1 D.coordinate 0) a.2
  let b : Mixed M n r := (Function.update a.1 D.coordinate (d+focus),a.2)
  have hcoord : E.coordinate = D.coordinate := rfl
  have hCoeff : E.coefficient = c := rfl
  have hFocus : D.extendedFocus a = focus := D.extendedFocus_active ha hu
  have hErase : Function.update b.1 D.coordinate 0 = Function.update a.1 D.coordinate 0 := by
    simp only [b,Function.update_idem]
  have hbFocus : D.focus (Function.update b.1 D.coordinate 0) b.2 = focus := by rw [hErase]
  have hFocusPoint : D.focusPoint b = D.focusPoint a := by
    simp only [focusPoint,b,Function.update_idem]
  have hBclose : vfValue (D.coefficient * D.focus (Function.update b.1 D.coordinate 0) b.2) <
      vfValue (b.1 D.coordinate - D.focus (Function.update b.1 D.coordinate 0) b.2) := by
    simpa only [hbFocus,b,Function.update_self,add_sub_cancel_right,hFocus] using hOld
  have hbA : b ∈ A.carrier := (D.core_membership_iff_focus b hu hBclose).mpr
    (hFocusPoint.symm ▸ hGraph)
  have hBF : D.extendedFocus b = focus := (D.extendedFocus_active hbA hu).trans hbFocus
  have hBEF : E.extendedFocus b = focus := hBF
  have hbOld : D.core b = true := by
    apply decide_eq_true_eq.mpr
    simpa only [hBF,b,Function.update_self,add_sub_cancel_right,hFocus] using hOld
  have hbNew : E.core b = false := by
    apply decide_eq_false_iff_not.mpr
    apply not_lt.mpr
    simpa only [hcoord,hCoeff,hBEF,b,Function.update_self,add_sub_cancel_right,hFocus] using hNew
  refine ⟨b,⟨hbA,hbOld,hbNew⟩,?_⟩
  change E.point b = _
  apply Prod.ext
  · simp only [point,hcoord,hbNew,Bool.false_eq_true,ite_false,add_zero,hBEF,
      b,Function.update_self,add_sub_cancel_right,Function.update_idem]
  · simp only [point,hbNew,b]

end DiamondIntegral.Section6.CentripetalData
