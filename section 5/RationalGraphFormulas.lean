import «section 5».NamedPolynomialTerms
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic

/-! One uniform named-coefficient formula for a rational graph piece:
the displayed denominator is nonzero and output times denominator equals
numerator. Its meaning is checked in every compatible target ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language FirstOrder.Ring

def rationalGraphFormula {n : ℕ} (p q : MvPolynomial (Fin n) ℂ) :
    (Language.ring[[ℂ]]).Formula (Fin n ⊕ Fin 1) :=
  ((namedPolynomialTerm (MvPolynomial.rename Sum.inl q)).equal
    (namedPolynomialTerm (0 : MvPolynomial (Fin n ⊕ Fin 1) ℂ))).not ⊓
  ((namedPolynomialTerm (MvPolynomial.X (.inr 0) * MvPolynomial.rename Sum.inl q -
    MvPolynomial.rename Sum.inl p)).equal (namedPolynomialTerm 0))

theorem rationalGraphFormula_realize {n : ℕ} (p q : MvPolynomial (Fin n) ℂ)
    (K : Type) [CommRing K] [CompatibleRing K] [(Language.ring[[ℂ]]).Structure K]
    [(Language.ring.lhomWithConstants ℂ).IsExpansionOn K] (c : ℂ →+* K)
    (hc : ∀ a, c a = ((Language.ring.con a : (Language.ring[[ℂ]]).Constants) : K))
    (x : Fin n → K) (y : K) :
    (rationalGraphFormula p q).Realize (Sum.elim x (fun _ => y)) ↔
      q.eval₂ c x ≠ 0 ∧ y * q.eval₂ c x = p.eval₂ c x := by
  have hterm (P : MvPolynomial (Fin n ⊕ Fin 1) ℂ) :
      (namedPolynomialTerm P).realize (Sum.elim x (fun _ => y)) = P.eval₂ c (Sum.elim x (fun _ => y)) :=
    namedPolynomialTerm_realize P K c hc _
  simp only [rationalGraphFormula, Formula.realize_inf, Formula.realize_not, Formula.realize_equal,
    hterm, MvPolynomial.eval₂_zero, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, Sum.elim_comp_inl, Sum.elim_inr, sub_eq_zero]

end DiamondIntegral.Section5
