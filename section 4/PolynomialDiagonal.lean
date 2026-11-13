module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff

/-! The diagonal polynomial map records each exponent in both variables.
It supplies the coefficient calculation for a polynomial grading coaction. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialDiagonal

variable {R : Type*} [CommRing R]

def diagonal : Polynomial R →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
    (Polynomial.monomial 1 Polynomial.X)

theorem diagonal_monomial (n : ℕ) (r : R) :
    diagonal (Polynomial.monomial n r) =
      Polynomial.monomial n (Polynomial.monomial n r) := by
  simp only [diagonal, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    RingHom.comp_apply, Polynomial.monomial_pow, one_mul,
    Polynomial.C_mul_monomial, Polynomial.C_mul_X_pow_eq_monomial]

theorem diagonal_coeff (p : Polynomial R) (n : ℕ) :
    (diagonal p).coeff n = Polynomial.monomial n (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial m r =>
    rw [diagonal_monomial]
    by_cases h : m = n
    · subst m; simp
    · simp [Polynomial.coeff_monomial, h]

end DiamondIntegral.Section4.PolynomialDiagonal
