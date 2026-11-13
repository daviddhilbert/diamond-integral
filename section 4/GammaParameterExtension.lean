import «section 4».GammaBaseExtension
import «section 2».AtomicBaseChange
import Mathlib.Data.Set.Finite.Range

/-! Naming a finite tuple of actual Gamma parameters preserves base
smallness and nontrivial definable Gamma. No RV lifts are asserted. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaParameterExtension
open GammaBaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem nontrivial_extend (B : Base (M := M)) (C : Set (Values.Gamma (M := M)))
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Section2.NontrivialDefinableGamma (withGamma B C) := by
  obtain ⟨γ, δ, hγ, hδ, hne⟩ := hΓ
  exact ⟨γ, δ, gammaSet_extend B C hγ, gammaSet_extend B C hδ, hne⟩

theorem finite_gamma_extension_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (B : Base (M := M)) (hγ : Cardinal.mk B.gamma < κ) {n : ℕ}
    (y : Fin n → Values.Gamma (M := M)) :
    Cardinal.mk (withGamma B (Set.range y)).gamma < κ := by
  let _ := (Set.finite_range y).to_subtype
  have hy : Cardinal.mk (Set.range y) < κ := (Cardinal.lt_aleph0_of_finite _).trans_le hκ
  apply lt_of_le_of_lt (Cardinal.mk_union_le _ _)
  exact Cardinal.add_lt_of_lt hκ hγ hy

end DiamondIntegral.Section4.GammaParameterExtension
