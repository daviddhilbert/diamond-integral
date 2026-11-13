import «section 3».RVUnitRectangularMonomials
import «section 3».TensorCoefficientRelations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def gammaGroundRVUnitCoordinateTupleMap
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (i : Fin n) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)) :=
  gammaGroundRVUnitRectangularMonomialMap A (fun (_ : Fin 1) j => if j = i then 1 else 0)

@[simp] theorem gammaGroundRVUnitCoordinateTupleMap_value
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (i : Fin n) (a : A) :
    (gammaGroundRVUnitCoordinateTupleMap A i a).val = fun _ : Fin 1 => a.val i := by
  funext j
  change (∏ k : Fin n, (a.val k) ^ (if k = i then (1 : ℤ) else 0)) = _
  simp

def gammaGroundRVUnitSparseTupleMap
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) 1)) (i : Fin n) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
  gammaGroundRVUnitRectangularMonomialMap A (fun j (_ : Fin 1) => if j = i then 1 else 0)

@[simp] theorem gammaGroundRVUnitSparseTupleMap_value
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) 1)) (i : Fin n) (a : A) :
    (gammaGroundRVUnitSparseTupleMap A i a).val =
      fun j : Fin n => if j = i then a.val 0 else 1 := by
  funext j
  change (∏ k : Fin 1, (a.val k) ^ (if j = i then (1 : ℤ) else 0)) = _
  simp

/-- Scalar availability uses a one-coordinate RV-unit map; a value is
available by existence, without a selected old-ground RV lift. -/
def GammaGroundRESAvailableValue (X : GammaGroundRESObject hc B r)
    (delta : Values.Gamma (M := M)) : Prop :=
  GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => delta)

def gammaGroundSparseValueTuple (i : Fin n) (delta : Values.Gamma (M := M)) :
    Fin n → Values.Gamma (M := M) := fun j => if j = i then delta else 1

theorem gammaGroundRESAvailableValueTuple_sparse_iff (X : GammaGroundRESObject hc B r)
    (i : Fin n) (delta : Values.Gamma (M := M)) :
    GammaGroundRESAvailableValueTuple X (gammaGroundSparseValueTuple i delta) ↔
      GammaGroundRESAvailableValue X delta := by
  constructor
  · rintro ⟨c,hcval⟩
    refine ⟨(gammaGroundRVUnitCoordinateTupleMap _ i).comp c,?_⟩
    intro a
    funext j
    change rvUnitValueHom (((gammaGroundRVUnitCoordinateTupleMap _ i) (c a)).val j) = delta
    rw [gammaGroundRVUnitCoordinateTupleMap_value]
    exact (congrFun (hcval a) i).trans (by simp [gammaGroundSparseValueTuple])
  · rintro ⟨c,hcval⟩
    refine ⟨(gammaGroundRVUnitSparseTupleMap _ i).comp c,?_⟩
    intro a
    funext j
    change rvUnitValueHom (((gammaGroundRVUnitSparseTupleMap _ i) (c a)).val j) = _
    rw [gammaGroundRVUnitSparseTupleMap_value]
    by_cases hj : j = i
    · subst j
      simp only [gammaGroundSparseValueTuple,if_pos rfl]
      exact congrFun (hcval a) (0 : Fin 1)
    · simp [hj,gammaGroundSparseValueTuple]
end DiamondIntegral.Section3
