import «section 6».RelativePolynomialRowFactors

/-! Actual RV-fibre anchors with the inactive VF coordinates equal,
and the derivative-row consequence of a nonzero partial Jacobian. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open Classical MvPolynomial
open SpecialTransformations.Section7
namespace DiamondIntegral.Section6
variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G] {n m : ℕ}

theorem exists_relative_rv_anchor (v : Valuation K G) (t s : Fin n → RVCalc.RV v)
    (i : Fin n) (hFixed : ∀ j,j ≠ i → t j = s j) :
    ∃ a : Fin (n+n) → K,a ∈ RVFibre v (productTuple t s) ∧
      ∀ j,j ≠ i → a (productRight n n j) = a (productLeft n n j) := by
  obtain ⟨x,hx⟩ := rvFibre_nonempty v t
  obtain ⟨z,hz⟩ := rvFibre_nonempty v s
  let y := Function.update x i (z i)
  have hy : y ∈ RVFibre v s := by
    intro j
    by_cases hj : j=i
    · subst j
      change RVCalc.rv v (Function.update x i (z i) i) = _
      rw [Function.update_self]
      exact hz i
    · change RVCalc.rv v (Function.update x i (z i) j) = _
      rw [Function.update_of_ne hj]
      exact (hx j).trans (hFixed j hj)
  refine ⟨productTuple x y,productTuple_mem_RVFibre v hx hy,fun j hj => ?_⟩
  rw [productTuple_right,productTuple_left]
  exact Function.update_of_ne hj _ _

theorem polynomial_partial_row_regular (F : Fin n → MvPolynomial (Fin m) K)
    (f : Fin n ↪ Fin m) (a : Fin m → K)
    (h : (partialJacobianPolynomial f F).eval a ≠ 0) (i : Fin n) :
    ∃ j,(pderiv (f j) (F i)).eval a ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  rw [partialJacobianPolynomial,RingHom.map_det]
  apply Matrix.det_eq_zero_of_row_eq_zero i
  exact hn

end DiamondIntegral.Section6
