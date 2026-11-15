import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Tactic.Ring

/-! Coefficient characters act by actual ring automorphisms of Hahn series.
This construction supplies the common action before restricting to Puiseux
series; it does not assume that a prescribed coefficient formula is a map. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
open scoped BigOperators
variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- Multiply each coefficient by a nonzero character value at its exponent. -/
def hahnCharacterTwist (χ : Multiplicative Γ →* kˣ) (f : HahnSeries Γ k) :
    HahnSeries Γ k where
  coeff g := (χ (Multiplicative.ofAdd g) : k) * f.coeff g
  isPWO_support' := f.isPWO_support.mono (by
    intro g hg h0
    exact hg (by simp [h0]))

omit [IsOrderedAddMonoid Γ] in
theorem hahnCharacterTwist_coeff (χ : Multiplicative Γ →* kˣ)
    (f : HahnSeries Γ k) (g : Γ) :
    (hahnCharacterTwist χ f).coeff g = (χ (Multiplicative.ofAdd g) : k) * f.coeff g := rfl

omit [IsOrderedAddMonoid Γ] in
theorem hahnCharacterTwist_support (χ : Multiplicative Γ →* kˣ)
    (f : HahnSeries Γ k) : (hahnCharacterTwist χ f).support = f.support := by
  ext g
  change ¬ (χ (Multiplicative.ofAdd g) : k) * f.coeff g = 0 ↔ ¬ f.coeff g = 0
  rw [mul_eq_zero, or_iff_right (χ (Multiplicative.ofAdd g)).ne_zero]

theorem hahnCharacterTwist_mul (χ : Multiplicative Γ →* kˣ)
    (f g : HahnSeries Γ k) :
    hahnCharacterTwist χ (f * g) = hahnCharacterTwist χ f * hahnCharacterTwist χ g := by
  classical
  ext z
  have ha : Finset.antidiagonal (hahnCharacterTwist χ f).isPWO_support
      (hahnCharacterTwist χ g).isPWO_support z =
      Finset.antidiagonal f.isPWO_support g.isPWO_support z := by
    ext ij
    simp only [Finset.mem_antidiagonal, hahnCharacterTwist_support]
  rw [hahnCharacterTwist_coeff, coeff_mul, Finset.mul_sum, coeff_mul, ha]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = z := (Finset.mem_antidiagonal.mp hij).2.2
  rw [hahnCharacterTwist_coeff, hahnCharacterTwist_coeff, ← he]
  change (χ (Multiplicative.ofAdd ij.1 * Multiplicative.ofAdd ij.2) : k) * _ = _
  rw [map_mul, Units.val_mul]
  ring

/-- The action is an automorphism, with inverse supplied by the inverse character. -/
def hahnCharacterEquiv (χ : Multiplicative Γ →* kˣ) :
    HahnSeries Γ k ≃+* HahnSeries Γ k where
  toFun := hahnCharacterTwist χ
  invFun := hahnCharacterTwist χ⁻¹
  left_inv f := by
    ext g
    simp [hahnCharacterTwist]
  right_inv f := by
    ext g
    simp [hahnCharacterTwist]
  map_mul' := hahnCharacterTwist_mul χ
  map_add' f g := by
    ext z
    exact mul_add _ _ _

theorem hahnCharacterEquiv_coeff (χ : Multiplicative Γ →* kˣ)
    (f : HahnSeries Γ k) (g : Γ) :
    (hahnCharacterEquiv χ f).coeff g = (χ (Multiplicative.ofAdd g) : k) * f.coeff g := rfl

/-- Character actions preserve the actual Hahn valuation, including zero. -/
theorem hahnCharacterEquiv_orderTop (χ : Multiplicative Γ →* kˣ)
    (f : HahnSeries Γ k) : (hahnCharacterEquiv χ f).orderTop = f.orderTop := by
  have hzero (z : Γ) : (hahnCharacterEquiv χ f).coeff z = 0 ↔ f.coeff z = 0 := by
    rw [hahnCharacterEquiv_coeff, mul_eq_zero, or_iff_right (χ (Multiplicative.ofAdd z)).ne_zero]
  apply le_antisymm
  · rw [le_orderTop_iff_forall]
    intro z hz
    exact (hzero z).mp (coeff_eq_zero_of_lt_orderTop hz)
  · rw [le_orderTop_iff_forall]
    intro z hz
    exact (hzero z).mpr (coeff_eq_zero_of_lt_orderTop hz)

end DiamondIntegral.Section5
