import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Character-line differences generate all finite direct-sum linear-action
differences. This is the quotient-ideal calculation in the comparison. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {R : Type*} [CommRing R] {ι : Type*}

def characterLineIdeal (line : ι → R) (trivial : R) : Ideal R :=
  Ideal.span (Set.range (fun i => line i - trivial))

def directSumCharacterIdeal (line : ι → R) (trivial : R) : Ideal R :=
  Ideal.span {x | ∃ n : ℕ, ∃ a : Fin n → ι, x = (∏ i, line (a i)) - trivial ^ n}

theorem character_product_difference_mem (line : ι → R) (trivial : R)
    (n : ℕ) (a : Fin n → ι) :
    (∏ i, line (a i)) - trivial ^ n ∈ characterLineIdeal line trivial := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_prod, map_pow]
  have he (i : Fin n) : Ideal.Quotient.mk (characterLineIdeal line trivial) (line (a i)) =
      Ideal.Quotient.mk (characterLineIdeal line trivial) trivial := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self (a i)))
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_self]

theorem directSumCharacterIdeal_eq_characterLineIdeal (line : ι → R) (trivial : R) :
    directSumCharacterIdeal line trivial = characterLineIdeal line trivial := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨n, a, rfl⟩
    exact character_product_difference_mem line trivial n a
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨1, fun _ => i, by simp⟩

theorem character_product_difference_multiple (line : ι → R) (trivial : R)
    (n : ℕ) (a : Fin n → ι) (x : R) :
    x * ((∏ i, line (a i)) - trivial ^ n) ∈ characterLineIdeal line trivial :=
  (characterLineIdeal line trivial).mul_mem_left x (character_product_difference_mem line trivial n a)

end DiamondIntegral.Section5
