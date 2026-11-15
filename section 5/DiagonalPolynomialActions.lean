import «section 5».EquivariantAffineEmbedding
import «section 5».AffineSchemeActions
import «section 5».FiniteKummerDescent

/-! Finite diagonal point actions have actual polynomial-algebra
automorphisms and scheme actions, with their complex-point formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
open PuiseuxOriginal

def polynomialDiagonalEquiv {n : ℕ} (w : Fin n → ℤ) (ζ : ℂˣ) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom (polynomialDiagonalAction w ζ) (polynomialDiagonalAction w ζ⁻¹)
    (by rw [← polynomialDiagonalAction_mul, mul_inv_cancel, polynomialDiagonalAction_one])
    (by rw [← polynomialDiagonalAction_mul, inv_mul_cancel, polynomialDiagonalAction_one])

def polynomialDiagonalHom {n : ℕ} (w : Fin n → ℤ) :
    ℂˣ →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) where
  toFun := polynomialDiagonalEquiv w
  map_one' := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun (polynomialDiagonalAction_one w) p
  map_mul' ζ ξ := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun (polynomialDiagonalAction_mul w ζ ξ) p

def finiteDiagonalAlgebraAction {n : ℕ} (N : ℕ+) (w : Fin n → ℤ) :
    rootsOfUnity (N : ℕ) ℂ →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) :=
  (polynomialDiagonalHom w).comp (rootsOfUnity (N : ℕ) ℂ).subtype

theorem polynomialDiagonalAction_point {n : ℕ} (w : Fin n → ℤ) (ζ : ℂˣ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    (fun i => (φ.comp (polynomialDiagonalAction w ζ)) (MvPolynomial.X i)) =
      weightedAction w ζ (fun i => φ (MvPolynomial.X i)) := by
  funext i
  simp [polynomialDiagonalAction, weightedAction]

end DiamondIntegral.Section5
