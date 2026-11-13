import «section 4».GammaMapOrder
import «section 4».GammaBoundedFamilies

/-! A definable proper box-radius map on every finite Gamma power.
Native multiplication is paper addition, so its sublevel sets are exactly
the symmetric boxes used in bounded Euler stabilization. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRadius
open GammaOrderLogic GammaDefinableMaps GammaMapOrder GammaBoundedFamilies

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def radius : (n : ℕ) → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)
  | 0, _ => 1
  | n + 1, z => max (max (z 0) (z 0)⁻¹) (radius n (Fin.tail z))

theorem radius_definable (B : Base (M := M)) (n : ℕ) : MapDefinable B (radius (M := M) n) := by
  induction n with
  | zero => exact constant_definable B 1 (GammaGroupNames.one_definable_base B)
  | succ n ih =>
    have h0 := projection_definable B (0 : Fin (n + 1))
    have htail := GammaDefinableMaps.reindex_definable B (radius n) ih Fin.succ
    have h := max_definable B _ _ (max_definable B _ _ h0 (inverse_definable B _ h0)) htail
    convert h using 1
    funext z
    change max (max (z 0) (z 0)⁻¹) (radius n (Fin.tail z)) =
      max (max (z 0) (z 0)⁻¹) (radius n (z ∘ Fin.succ))
    have he : Fin.tail z = z ∘ Fin.succ := by funext i; rfl
    rw [he]

theorem one_le_radius (n : ℕ) (z : Fin n → Values.Gamma (M := M)) : 1 ≤ radius n z := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (ih (Fin.tail z)).trans (le_max_right _ _)

theorem coordinate_le_radius (n : ℕ) (z : Fin n → Values.Gamma (M := M)) (i : Fin n) :
    z i ≤ radius n z := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (ih (Fin.tail z) j).trans (le_max_right _ _)

theorem inverse_coordinate_le_radius (n : ℕ) (z : Fin n → Values.Gamma (M := M)) (i : Fin n) :
    (z i)⁻¹ ≤ radius n z := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (ih (Fin.tail z) j).trans (le_max_right _ _)

theorem radius_bounds (n : ℕ) (z : Fin n → Values.Gamma (M := M)) (i : Fin n) :
    (radius n z)⁻¹ ≤ z i ∧ z i ≤ radius n z := by
  refine ⟨?_, coordinate_le_radius n z i⟩
  have h := inv_le_inv_iff.mpr (inverse_coordinate_le_radius n z i)
  simpa only [inv_inv] using h

theorem radius_le_iff (n : ℕ) (z : Fin n → Values.Gamma (M := M)) (r : Values.Gamma (M := M))
    (hr : 1 ≤ r) : radius n z ≤ r ↔ ∀ i, r⁻¹ ≤ z i ∧ z i ≤ r := by
  constructor
  · intro h i
    have hi := radius_bounds n z i
    exact ⟨(inv_le_inv_iff.mpr h).trans hi.1, hi.2.trans h⟩
  · intro h
    induction n with
    | zero => exact hr
    | succ n ih =>
      apply max_le
      · apply max_le (h 0).2
        have hi := inv_le_inv_iff.mpr (h 0).1
        simpa only [inv_inv] using hi
      · exact ih (Fin.tail z) (fun i => h i.succ)

end DiamondIntegral.Section4.GammaRadius
