import «section 3».GammaGroundUnaryAffineCriterion
import «section 3».RVUnitGammaMaps
import «section 3».IntegerMonomialMaps
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Arbitrary source/target Gamma tuples have finite piecewise integral-
affine formulas with actual old-ground RV shifts. No bijectivity or
unimodularity is required in this predicate. -/
def GammaGroundPiecewiseIntegralAffine
    {I : GammaGroundGammaPiece hc B n} {J : GammaGroundGammaPiece hc B m} (h : GammaGroundMap I J) : Prop :=
  ∃ N : ℕ, ∃ P : Fin N → GammaGroundGammaPiece hc B n,
    ∃ linear : Fin N → Matrix (Fin m) (Fin n) ℤ,
    ∃ shift : Fin N → Fin m → (CanonicalRV.RVSort M)ˣ,
      (∀ i, (P i).carrier ⊆ I.carrier) ∧
      (∀ γ : I, ∃! i, γ.val ∈ (P i).carrier) ∧
      (∀ i j, DefinableClosureAtBase B .rv (rvUnitValues (shift i) j)) ∧
      ∀ i (γ : I), γ.val ∈ (P i).carrier →
        (h γ).val = rvUnitTupleValues (shift i) *
          integerMonomialMap (G := Values.Gamma (M := M)) (linear i) γ.val

end DiamondIntegral.Section3
