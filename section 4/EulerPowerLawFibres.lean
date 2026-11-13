module

public import «section 4».EulerRationalBranches
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Torsion

/-! A finite power-law cover bounds all fibres outside a finite set of
constant-branch values. This statement is pure ordered-group algebra. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [RootableBy G ℕ]

theorem finite_large_power_law_fibres (D : Set G) (T : G → G) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (c : Fin m → G) (hq : ∀ i, q i ≠ 0)
    (hcover : ∀ x ∈ D, ∃ i, T x ^ q i = c i * x ^ p i) :
    {y : G | ∃ u : Fin (m + 1) → G, Function.Injective u ∧
      ∀ j, u j ∈ D ∧ T (u j) = y}.Finite := by
  let v : Fin m → G := fun i => RootableBy.root (c i) (q i)
  apply (Set.finite_range v).subset
  rintro y ⟨u, hu, hDu⟩
  by_contra hy
  have hnot (i : Fin m) : y ≠ v i := fun he => hy ⟨i, he.symm⟩
  have hc (j : Fin (m + 1)) : ∃ i, y ^ q i = c i * u j ^ p i := by
    obtain ⟨i, hi⟩ := hcover (u j) (hDu j).1
    exact ⟨i, (hDu j).2 ▸ hi⟩
  choose index hindex using hc
  have hp (j : Fin (m + 1)) : p (index j) ≠ 0 := by
    intro hz
    have he : y ^ q (index j) = c (index j) := by
      simpa only [hz, zpow_zero, mul_one] using hindex j
    apply hnot (index j)
    apply HasUniqueRoots.pow_left_injective (hq (index j))
    exact he.trans (RootableBy.root_cancel (c (index j)) (hq (index j))).symm
  have hi : Function.Injective index := by
    intro a b hab
    apply hu
    apply zpow_left_injective (hp a)
    apply mul_left_cancel (a := c (index a))
    exact (hindex a).symm.trans (by simpa only [hab] using hindex b)
  have hcard := Fintype.card_le_of_injective index hi
  simp only [Fintype.card_fin] at hcard
  omega

end DiamondIntegral.Section4.EulerFunction
