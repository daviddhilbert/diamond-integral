import «section 3».GammaMonomialArity
import «section 3».RVAngularInverseMonomials
import «section 3».GammaGroundAngularFiniteValues
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n k : ℕ}

theorem RVAngularCell.inverseResidueCoefficient_value_definable
    {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)} (E : RVAngularCell A)
    (K : Section2.ZeroFaceChart (Set.range E.active))
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ)
    (hr : ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues r j)) (i : Fin n) :
    GammaDefinableClosureAtBase B (rvUnitValueHom (E.inverseResidueCoefficient K r i)) := by
  have h := gammaDefinableClosure_integerCharacter
    (fun j => integerBasisInverseMatrix E.basis i (K.zeroIndex j)) (rvUnitTupleValues r) hr
  have he : rvUnitValueHom (E.inverseResidueCoefficient K r i) =
      integerCharacter (fun j => integerBasisInverseMatrix E.basis i (K.zeroIndex j)) (rvUnitTupleValues r) := by
    simp only [RVAngularCell.inverseResidueCoefficient,integerMonomialMap,integerCharacter,map_prod,map_zpow,rvUnitTupleValues]
  exact he.symm ▸ h

/-- A cell containing a Gamma-independent input k-tuple needs at least
k free monomial coordinates. -/
theorem gammaGroundRVAngularCell_generic_projection_arity_le
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I : Fin k → Fin n) (x : X)
    (hγ : GammaTupleIndependentOver B (fun i => rvUnitValueHom (x.val (I i)))) : k ≤ K.freeArity := by
  let r := (E.coordinateEquiv K x.val).1
  let u := (E.coordinateEquiv K x.val).2
  let c := fun i => rvUnitValueHom (E.inverseResidueCoefficient K r (I i))
  let F := Matrix.submatrix (E.inverseFreeMatrix K) I id
  have hr : ∀ j, GammaDefinableClosureAtBase B (rvUnitTupleValues r j) :=
    gammaGroundRVAngularCell_residue_values_definable X E K x
  have hc : ∀ i, GammaDefinableClosureAtBase B (c i) := fun i =>
    E.inverseResidueCoefficient_value_definable K r hr (I i)
  have he : (fun i => rvUnitValueHom (x.val (I i))) = c * integerMonomialMap F (rvUnitTupleValues u) := by
    have hx : (E.coordinateEquiv K).symm (r,u) = x.val := (E.coordinateEquiv K).symm_apply_apply x.val
    funext i
    have hh := congrArg (fun z => rvUnitValueHom (z (I i))) (E.coordinateEquiv_symm_monomial K r u)
    rw [hx] at hh
    change rvUnitValueHom (x.val (I i)) = rvUnitValueHom (E.inverseResidueCoefficient K r (I i) *
      integerMonomialMap (E.inverseFreeMatrix K) u (I i)) at hh
    rw [map_mul] at hh
    exact hh.trans (by simp only [integerMonomialMap,map_prod,map_zpow]; rfl)
  exact gammaTupleIndependent_monomial_arity_le F c hc (rvUnitTupleValues u) (he ▸ hγ)
end DiamondIntegral.Section3
