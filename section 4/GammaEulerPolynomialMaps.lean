import «section 4».GammaEulerEvaluation

/-! Ordinary Gamma polynomial evaluation commutes with target ring maps.
At T=0 it kills every homogeneous positive-degree polynomial, while the
constant-coefficient restriction is retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaEulerEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem polynomial_map (B : Base (M := M)) (k : EulerKind) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (p : GammaFunctionPolynomial.sourceRing B k) :
    f (polynomial B k t p) = polynomial B k (f t) p := by
  change f (Polynomial.eval₂ ((Int.castRingHom R).comp (coefficientEuler B k)) t p.val) =
    Polynomial.eval₂ ((Int.castRingHom S).comp (coefficientEuler B k)) (f t) p.val
  induction p.val using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow]
    exact congrArg (fun z : S => z * f t ^ n) (map_intCast f (coefficientEuler B k a))

theorem polynomial_zero_of_mem (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    {n : ℕ} (hn : n ≠ 0) (p : GammaFunctionPolynomial.sourceRing B k)
    (hp : p ∈ GammaPolynomialGradings.unboundedPiece B k n) : polynomial B k (0 : R) p = 0 := by
  change Polynomial.eval₂ ((Int.castRingHom R).comp (coefficientEuler B k)) (0 : R) p.val = 0
  rw [(GammaPolynomialGradings.mem_unboundedPiece B k p n).mp hp, Polynomial.eval₂_monomial, zero_pow hn, mul_zero]

end DiamondIntegral.Section4.GammaEulerEvaluation
