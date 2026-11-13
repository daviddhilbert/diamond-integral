import «section 3».GammaGroundAngularFiniteValues
import «section 3».RVAngularValueReconstruction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- No nonzero integral character of the tuple has an old-ground
Gamma-definable value. This is independence modulo the old Gamma closure. -/
def GammaTupleIndependentOver (B : Base (M := M)) (γ : Fin n → Values.Gamma (M := M)) : Prop :=
  ∀ e : Fin n → ℤ, GammaDefinableClosureAtBase B (integerCharacter e γ) → e = 0

theorem gammaGroundRVAngularCell_residueArity_zero
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (x : X) (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) : E.residueArity = 0 := by
  by_contra hn
  let i : Fin E.residueArity := ⟨0,Nat.pos_of_ne_zero hn⟩
  let K := Section2.zeroFaceChart (Set.range E.active)
  obtain ⟨j,hj⟩ := coordinateProductChart_fixed_cover K (E.active i) (Set.mem_range_self i)
  have hd := gammaGroundRVAngularCell_residue_values_definable X E K x j
  have he : integerCharacter (E.basis (E.active i)) (rvUnitTupleValues x.val) =
      rvUnitTupleValues (E.coordinateEquiv K x.val).1 j := by
    rw [hj]
    exact congrArg (fun p => p.1 j) (E.coordinate_value_naturality K x.val)
  have hz : E.basis (E.active i) = 0 := hγ _ (he.symm ▸ hd)
  exact E.basis.ne_zero (E.active i) hz

theorem gammaGroundRVAngularCell_generic_fibre_invariant
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier)
    (x : X) (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (y : Fin n → (CanonicalRV.RVSort M)ˣ) (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y) :
    y ∈ X.carrier := by
  have hr := gammaGroundRVAngularCell_residueArity_zero X E x hγ
  apply E.invariant x.val x.property y
  · intro i
    exact False.elim (by simpa [hr] using i.isLt)
  · intro j _
    have he := congrArg (integerMonomialBasisEquiv (G := Values.Gamma (M := M)) E.basis) hxy
    have hx := monomial_map_value (rvUnitValueHom (M := M)) (integerBasisMatrix E.basis) x.val
    have hy := monomial_map_value (rvUnitValueHom (M := M)) (integerBasisMatrix E.basis) y
    exact (congrFun hx j).trans ((congrFun he j).trans (congrFun hy j).symm)
end DiamondIntegral.Section3
