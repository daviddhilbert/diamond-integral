import «section 6».RelativeApertureHomeomorphism

/-! Membership throughout an old contracted ball is exactly membership
of its focus graph. This applies to every actual protected component,
and hence to every released annulus after an aperture increase. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.RelativeApertureData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def focusPoint (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : Mixed M n r :=
  (Function.update p.1 D.coordinate (D.focus (Function.update p.1 D.coordinate 0) p.2),p.2)

theorem focusPoint_erase (D : RelativeApertureData (G := G) A) (p : Mixed M n r) :
    Function.update (D.focusPoint p).1 D.coordinate 0 = Function.update p.1 D.coordinate 0 := by
  funext i
  by_cases hi : i = D.coordinate
  · subst i
    simp only [focusPoint,Function.update_self]
  · simp only [focusPoint,Function.update_of_ne hi]

theorem core_membership_iff_focus (D : RelativeApertureData (G := G) A) (p : Mixed M n r)
    (hu : p.2 ∈ D.activeTags.carrier)
    (hclose : vfValue (D.endpoint (Function.update p.1 D.coordinate 0) p.2) <
      vfValue (p.1 D.coordinate - D.focus (Function.update p.1 D.coordinate 0) p.2)) :
    p ∈ A.carrier ↔ D.focusPoint p ∈ A.carrier := by
  obtain ⟨α,β,_,_,hInv,_,hdom⟩ := D.covariance p.2 hu
  have hCong (hbound : α.val ≤ vfValue (D.endpoint (Function.update p.1 D.coordinate 0) p.2)) :
      Congruent (fun i => if i = D.coordinate then α else β i) p.1 (D.focusPoint p).1 := by
    intro i
    by_cases hi : i = D.coordinate
    · subst i
      simpa only [ite_true,focusPoint,Function.update_self] using hbound.trans_lt hclose
    · simpa only [hi,ite_false,focusPoint,Function.update_of_ne hi,sub_self,valueHom_eq_value]
        using gamma_lt_value_zero (β i)
  constructor
  · intro hp
    exact (hInv p.1 (D.focusPoint p).1 (hCong (hdom p.1 hp))).mp hp
  · intro hp
    have hbound : α.val ≤ vfValue (D.endpoint (Function.update p.1 D.coordinate 0) p.2) := by
      have hh := hdom (D.focusPoint p).1 hp
      rw [D.focusPoint_erase p] at hh
      exact hh
    exact (hInv p.1 (D.focusPoint p).1 (hCong hbound)).mpr hp

end DiamondIntegral.Section6.RelativeApertureData
