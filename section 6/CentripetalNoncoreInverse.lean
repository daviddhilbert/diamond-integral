import «section 6».ContinuousCoordinateRootStep

/-! Actual inverse points on the noncore annulus of a permitted
component over an RV-pullback. This works in every VF coordinate and
does not require the focus to be constant in its complementary inputs. -/

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

theorem noncore_point_inverse (D : CentripetalData (G := G) A) (hA : IsRVPullback A.carrier)
    (a : Mixed M n r) (ha : a ∈ A.carrier) (hu : a.2 ∈ D.activeTags.carrier) (y : VF M)
    (hSmall : vfValue (D.extendedFocus a) < vfValue y)
    (hCut : vfValue y ≤ vfValue (D.coefficient*D.extendedFocus a)) :
    ∃ b, b ∈ A.carrier ∧ D.core b = false ∧
      D.point b = (Function.update a.1 D.coordinate y,
        Fin.append (fun _ : Fin 1 => branchTag (M := M) false) a.2) := by
  let focus := D.extendedFocus a
  let b : Mixed M n r := (Function.update a.1 D.coordinate (focus+y),a.2)
  have hf0 : focus ≠ 0 := D.focus_nonzero ha hu
  have hSame : rv M (focus+y) = rv M (a.1 D.coordinate) := by
    have he : rv M (focus+y) = rv M focus := (rv_eq_iff_value_close hf0).mpr (by
      simpa only [add_sub_cancel_left] using hSmall)
    have hFocusRV : rv M focus = rv M (a.1 D.coordinate) := by
      rw [show focus = D.focus (Function.update a.1 D.coordinate 0) a.2 from D.extendedFocus_active ha hu]
      exact D.focusRV a ha hu
    exact he.trans hFocusRV
  have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
    funext i
    by_cases hi : i = D.coordinate
    · subst i
      change rv M (a.1 D.coordinate) = rv M (b.1 D.coordinate)
      simpa only [b,Function.update_self] using hSame.symm
    · change rv M (a.1 i) = rv M (b.1 i)
      simp only [b,Function.update_of_ne hi]) rfl
  have hFocus : D.extendedFocus b = focus := (D.extendedFocus_same_other ha hb rfl
    (fun i hi => by simp only [b,Function.update_of_ne hi])).symm
  have hCore : D.core b = false := by
    apply decide_eq_false_iff_not.mpr
    apply not_lt.mpr
    simpa only [hFocus,b,Function.update_self,add_sub_cancel_left,focus] using hCut
  refine ⟨b,hb,hCore,?_⟩
  apply Prod.ext
  · simp only [point,hCore,Bool.false_eq_true,ite_false,add_zero,hFocus,b,
      Function.update_self,add_sub_cancel_left,Function.update_idem]
  · simp only [point,hCore,b]

end DiamondIntegral.Section6.CentripetalData
