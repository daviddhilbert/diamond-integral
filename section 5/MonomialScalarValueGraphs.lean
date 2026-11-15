import «section 3».RVUnitValueHom
import Mathlib.Algebra.Group.Torsion

/-! A scalar Gamma-valued graph has single-valued value projection on
each fixed-value monomial rectangle. This uses no angular section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
open DiamondIntegral.Section3
variable {R G : Type} [CommGroup R] [CommGroup G] [IsMulTorsionFree G]
variable {n a : ℕ}

theorem monomial_scalar_graph_value_unique
    (v : R →* G) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (active : Fin a → Fin (n+1)) (X : Set (Fin (n+1) → R))
    (hfixed : ∀ x ∈ X, ∀ y ∈ X, ∀ i,
      v (integerMonomialMap A x (active i)) = v (integerMonomialMap A y (active i)))
    (hrect : ∀ x ∈ X, ∀ y ∈ X, ∀ z,
      (∀ i, integerMonomialMap A z (active i) = integerMonomialMap A x (active i)) →
      (∀ j, v (z j) = v (y j)) → z ∈ X)
    (hgraph : ∀ x ∈ X, ∀ y ∈ X,
      (∀ j : Fin n, x j.castSucc = y j.castSucc) → v (x (Fin.last n)) = v (y (Fin.last n)))
    (x y : Fin (n+1) → R) (hx : x ∈ X) (hy : y ∈ X)
    (hvalues : ∀ j : Fin n, v (x j.castSucc) = v (y j.castSucc)) :
    v (x (Fin.last n)) = v (y (Fin.last n)) := by
  by_cases ha : ∃ i, A (active i) (Fin.last n) ≠ 0
  · obtain ⟨i, hi⟩ := ha
    have he := hfixed x hx y hy i
    simp only [integerMonomialMap, map_prod, map_mul, map_zpow, Fin.prod_univ_castSucc] at he
    have hp : (∏ j : Fin n, v (x j.castSucc) ^ A (active i) j.castSucc) =
        ∏ j : Fin n, v (y j.castSucc) ^ A (active i) j.castSucc := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hvalues j]
    rw [hp] at he
    exact (Commute.all _ _).eq_of_zpow_eq_zpow hi (mul_left_cancel he)
  · have hzexp : ∀ i, A (active i) (Fin.last n) = 0 := by
      intro i
      by_contra h
      exact ha ⟨i, h⟩
    let z : Fin (n+1) → R := Fin.snoc (Fin.init x) (y (Fin.last n))
    have hz : z ∈ X := by
      apply hrect x hx y hy z
      · intro i
        simp only [integerMonomialMap, Fin.prod_univ_castSucc, z, Fin.snoc_last,
          Fin.snoc_castSucc, Fin.init, hzexp, zpow_zero, mul_one]
      · intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp only [z, Fin.snoc_last]
        · simpa only [z, Fin.snoc_castSucc, Fin.init] using hvalues k
    have he := hgraph x hx z hz (by intro j; simp only [z, Fin.snoc_castSucc, Fin.init])
    simpa only [z, Fin.snoc_last] using he

end DiamondIntegral.Section5
