import «section 3».IntegerRectangularKernel
import «section 3».IntegerCharacterComposition
import «section 3».FullGammaFunctionEvaluation
import «section 3».GammaGenericAngularCells
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

theorem gammaDefinableClosure_integerCharacter (e : Fin n → ℤ) (c : Fin n → Values.Gamma (M := M))
    (hc : ∀ i, GammaDefinableClosureAtBase B (c i)) :
    GammaDefinableClosureAtBase B (integerCharacter e c) := by
  exact (FullGammaFunction.prod Finset.univ (fun i (z : Fin n → Values.Gamma (M := M)) => z i ^ e i)
    (fun i _ => (FullGammaFunction.proj (integrationGammaBase B) i).zpow (e i))).eval_definable c hc

/-- A Gamma-independent n-tuple cannot be reconstructed from fewer than
n free values by integral monomials and old-ground definable coefficients. -/
theorem gammaTupleIndependent_monomial_arity_le
    (A : Matrix (Fin n) (Fin m) ℤ) (c : Fin n → Values.Gamma (M := M))
    (hc : ∀ i, GammaDefinableClosureAtBase B (c i)) (u : Fin m → Values.Gamma (M := M))
    (hγ : GammaTupleIndependentOver B (c * integerMonomialMap A u)) : n ≤ m := by
  by_contra h
  obtain ⟨e,he,hA⟩ := integerMatrix_left_kernel_of_fewer_columns A (Nat.lt_of_not_ge h)
  have hzero : (fun j => ∑ i, e i * A i j) = 0 := funext hA
  have hv : integerCharacter e (c * integerMonomialMap A u) = integerCharacter e c := by
    rw [integerCharacter_mul,integerCharacter_monomialMap,hzero,integerCharacter_zero,mul_one]
  exact he (hγ e (hv.symm ▸ gammaDefinableClosure_integerCharacter e c hc))
end DiamondIntegral.Section3
