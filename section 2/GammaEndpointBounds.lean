import «section 2».GammaAbsoluteValues
import «section 2».GammaAffineBounds

/-! The absolute-value bound determined by the two finite endpoints of
a nonempty bounded Gamma set. This is the endpoint expression in 2.53. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaAbs_image_isLUB {A : Set (Gamma M)} {α β : Gamma M}
    (hα : IsGLB A α) (hβ : IsLUB A β) :
    IsLUB (gammaAbs '' A) (max β α⁻¹) := by
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    exact max_le ((hβ.1 ha).trans (le_max_left _ _))
      ((inv_le_inv' (hα.1 ha)).trans (le_max_right _ _))
  · intro c hc
    apply max_le
    · apply hβ.2
      intro a ha
      exact (le_max_left a a⁻¹).trans (hc ⟨a,ha,rfl⟩)
    · have hl : c⁻¹ ∈ lowerBounds A := by
        intro a ha
        exact (gammaAbs_le_iff a c).mp (hc ⟨a,ha,rfl⟩) |>.1
      simpa only [inv_inv] using inv_le_inv' (hα.2 hl)

theorem gamma_endpoint_bound_eq {A : Set (Gamma M)} (hne : A.Nonempty)
    {α β : Gamma M} (hα : IsGLB A α) (hβ : IsLUB A β) :
    max (max (gammaAbs α) (gammaAbs β)) 1 = max β α⁻¹ := by
  obtain ⟨a,ha⟩ := hne
  have hab : α ≤ β := (hα.1 ha).trans (hβ.1 ha)
  have h1 : (1 : Gamma M) ≤ max β α⁻¹ := by
    by_cases hb : 1 ≤ β
    · exact hb.trans (le_max_left _ _)
    · have ha1 : α ≤ 1 := hab.trans (le_of_lt (lt_of_not_ge hb))
      have hi : (1 : Gamma M) ≤ α⁻¹ := by simpa using inv_le_inv' ha1
      exact hi.trans (le_max_right _ _)
  apply le_antisymm
  · apply max_le _ h1
    apply max_le
    · exact max_le (hab.trans (le_max_left _ _)) (le_max_right _ _)
    · exact max_le (le_max_left _ _) ((inv_le_inv' hab).trans (le_max_right _ _))
  · apply max_le
    · exact (le_max_left β β⁻¹).trans ((le_max_right (gammaAbs α) (gammaAbs β)).trans (le_max_left _ _))
    · exact (le_max_right α α⁻¹).trans ((le_max_left (gammaAbs α) (gammaAbs β)).trans (le_max_left _ _))

end DiamondIntegral.Section2
