import «section 6».WeightedPolynomialRowFormulas

/-! The exact inactive-row factor in a weighted lifting system. Equal
integer coefficients would give a squared diagonal equation, whose
entire derivative row vanishes at a diagonal anchor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open Classical MvPolynomial
open SpecialTransformations.Section7
namespace DiamondIntegral.Section6
variable {K : Type*} [Field K] {n : ℕ}

theorem relative_diagonal_row_factor (j : Fin n) (p q : ℤ)
    (H : MvPolynomial (Fin (n+n)) K)
    (hH : H = p • ((X (productLeft n n j) *
      pderiv (productLeft n n j) (relativeDiagonalPolynomial K n j)) * relativeDiagonalPolynomial K n j) +
      q • ((X (productRight n n j) *
        pderiv (productRight n n j) (relativeDiagonalPolynomial K n j)) * relativeDiagonalPolynomial K n j)) :
    H = (q • X (productRight n n j) - p • X (productLeft n n j)) * relativeDiagonalPolynomial K n j := by
  have hParts := relativeDiagonalPolynomial_partials (K := K) j
  rw [hH,hParts.1,hParts.2]
  simp only [zsmul_eq_mul]
  ring

theorem relative_diagonal_square_derivative_zero (j : Fin n) (p : ℤ)
    (a : Fin (n+n) → K) (ha : a (productRight n n j) = a (productLeft n n j))
    (l : Fin (n+n)) :
    (pderiv l (p • (relativeDiagonalPolynomial K n j * relativeDiagonalPolynomial K n j))).eval a = 0 := by
  have hD : (relativeDiagonalPolynomial K n j).eval a = 0 := by
    change (MvPolynomial.eval a) (X (productRight n n j) - X (productLeft n n j)) = 0
    rw [(MvPolynomial.eval a).map_sub,MvPolynomial.eval_X,MvPolynomial.eval_X,ha,sub_self]
  rw [_root_.map_zsmul (pderiv (R := K) l) p
      (relativeDiagonalPolynomial K n j * relativeDiagonalPolynomial K n j),pderiv_mul,
    _root_.map_zsmul (MvPolynomial.eval a) p _,
    (MvPolynomial.eval a).map_add,(MvPolynomial.eval a).map_mul,(MvPolynomial.eval a).map_mul,hD]
  simp only [zero_mul,mul_zero,add_zero,smul_zero]

theorem relative_diagonal_row_coefficients_ne (j : Fin n) (p q : ℤ)
    (H : MvPolynomial (Fin (n+n)) K)
    (hH : H = (q • X (productRight n n j) - p • X (productLeft n n j)) * relativeDiagonalPolynomial K n j)
    (a : Fin (n+n) → K) (ha : a (productRight n n j) = a (productLeft n n j))
    (hRegular : ∃ l,(pderiv l H).eval a ≠ 0) : p ≠ q := by
  intro hpq
  subst q
  have hSquare : H = p • (relativeDiagonalPolynomial K n j * relativeDiagonalPolynomial K n j) := by
    rw [hH,← smul_sub,smul_mul_assoc]
    rfl
  obtain ⟨l,hl⟩ := hRegular
  rw [hSquare] at hl
  exact hl (relative_diagonal_square_derivative_zero j p a ha l)

end DiamondIntegral.Section6
