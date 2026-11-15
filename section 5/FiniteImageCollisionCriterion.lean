import «section 5».FiniteFibreValidity

/-! Finiteness with a fixed image bound is equivalent to excluding a
fixed tuple of source points with pairwise distinct images. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical

theorem finite_image_bound_iff_no_distinct_rows {X Y : Type*} (f : X → Y) (S : Set X) (N : ℕ) :
    (f '' S).Finite ∧ (f '' S).ncard ≤ N ↔
      ¬ ∃ x : Fin (N + 1) → X, (∀ i, x i ∈ S) ∧ Function.Injective (f ∘ x) := by
  rw [← no_injective_fin_iff_card_bound]
  constructor
  · intro h ⟨x, hx, hi⟩
    let g : Fin (N + 1) → f '' S := fun i => ⟨f (x i), x i, hx i, rfl⟩
    exact h g (fun i j hij => hi (congrArg Subtype.val hij))
  · intro h g hg
    have hx (i : Fin (N + 1)) : ∃ x, x ∈ S ∧ f x = (g i).val := (g i).property
    choose x hxS hxf using hx
    apply h
    refine ⟨x, hxS, ?_⟩
    intro i j hij
    apply hg
    apply Subtype.ext
    exact (hxf i).symm.trans (hij.trans (hxf j))

end DiamondIntegral.Section5
