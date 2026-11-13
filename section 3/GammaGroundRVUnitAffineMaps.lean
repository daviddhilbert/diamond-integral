import «section 3».GammaGroundConstants
import «section 3».RVUnitTupleOperations
import «section 3».RVUnitRectangularMonomials
import «section 3».GammaGroundRVGenericScalarContraction
import «section 3».UnimodularMonomialFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- An actual original-ground coefficient tuple supplies the full
monomial RV map, on any original-ground unit domain. -/
def gammaGroundRVUnitAffineMap (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (C : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c}) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) := by
  let U := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)
  let p := (GammaGroundMap.const (R := rawRVUnitSpace n) A c hcdef).pair (gammaGroundRVUnitRectangularMonomialMap A C)
  exact (gammaGroundRVUnitTupleMulMap (U.prod U)).comp p

@[simp] theorem gammaGroundRVUnitAffineMap_formula
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (C : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c}) (a : A) :
    (gammaGroundRVUnitAffineMap A C c hcdef a).val = c * integerMonomialMap C a.val := rfl

theorem gammaGroundRVUnitAffineMap_values
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (C : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hcdef : GammaGroundDefinable hc B (rawRVUnitSpace n) {c}) (a : A) :
    rvUnitTupleValues (gammaGroundRVUnitAffineMap A C c hcdef a).val =
      rvUnitTupleValues c * integerMonomialMap C (rvUnitTupleValues a.val) := by
  rw [gammaGroundRVUnitAffineMap_formula]
  funext i
  change rvUnitValueHom (c i * integerMonomialMap C a.val i) = _
  rw [map_mul]
  exact congrArg (fun z => rvUnitValueHom (c i) * z)
    (congrFun (monomial_map_value (rvUnitValueHom (M := M)) C a.val) i)

end DiamondIntegral.Section3
