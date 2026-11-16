import «section 6».CoordinateBundleCriterion

/-! Release geometry for an old aperture depending on retained RV labels.
The old radius need not come from one globally named VF coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem variable_aperture_coordinate_replacement
    (D : CentripetalData (G := G) A) (ρ : (Fin r → RVInfinity M) → Gamma M)
    (hStable : ∀ p ∈ A.carrier, p.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (ρ p.2).val < vfValue (p.1 D.coordinate-x) →
        (Function.update p.1 D.coordinate x,p.2) ∈ A.carrier)
    (a : Mixed M n r) (ha : a ∈ A.carrier) (hu : a.2 ∈ D.activeTags.carrier)
    (hOld : (ρ a.2).val < vfValue (a.1 D.coordinate-D.extendedFocus a))
    (hNew : D.core a=false) (d : VF M)
    (hrv : rv M d=rv M ((D.point a).1 D.coordinate)) :
    ∃ b, b ∈ A.carrier ∧ b.2=a.2 ∧ b.2 ∈ D.activeTags.carrier ∧
      (ρ b.2).val < vfValue (b.1 D.coordinate-D.extendedFocus b) ∧ D.core b=false ∧
      D.point b=(Function.update (D.point a).1 D.coordinate d,(D.point a).2) := by
  let focus := D.extendedFocus a
  let b : Mixed M n r := (Function.update a.1 D.coordinate (d+focus),a.2)
  have hValue : vfValue d=vfValue (a.1 D.coordinate-focus) := by
    have he : (D.point a).1 D.coordinate=a.1 D.coordinate-focus := by
      simp only [point,Function.update_self,hNew,Bool.false_eq_true,ite_false,add_zero,focus]
    exact (congrArg Values.vrv hrv).trans (congrArg vfValue he)
  have hClose : (ρ a.2).val < vfValue (a.1 D.coordinate-(d+focus)) := by
    have hmin : min (vfValue (a.1 D.coordinate-focus)) (vfValue d) ≤
        vfValue (a.1 D.coordinate-(d+focus)) := by
      have he : a.1 D.coordinate-(d+focus)=(a.1 D.coordinate-focus)-d := by ring
      rw [he]
      exact vfValue_min_le_sub (a.1 D.coordinate-focus) d
    exact (lt_min hOld (hValue.symm ▸ hOld)).trans_le hmin
  have hb : b ∈ A.carrier := hStable a ha hu (d+focus) hClose
  have hFocus : D.extendedFocus b=focus := by
    apply D.extendedFocus_same_other hb ha rfl
    intro i hi
    exact Function.update_of_ne hi _ _
  have hbOld : (ρ b.2).val < vfValue (b.1 D.coordinate-D.extendedFocus b) := by
    simpa only [b,Function.update_self,hFocus,add_sub_cancel_right,hValue] using hOld
  have hbNew : D.core b=false := by
    apply decide_eq_false_iff_not.mpr
    have hn := decide_eq_false_iff_not.mp hNew
    simpa only [core,b,Function.update_self,hFocus,add_sub_cancel_right,hValue,focus] using hn
  refine ⟨b,hb,rfl,hu,hbOld,hbNew,?_⟩
  apply Prod.ext
  · simp only [point,hNew,hbNew,Bool.false_eq_true,ite_false,add_zero,hFocus,
      b,Function.update_self,add_sub_cancel_right,Function.update_idem,focus]
  · simp only [point,hNew,hbNew,b]

end DiamondIntegral.Section6.CentripetalData
