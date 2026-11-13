import «section 3».RVAngularQuotient
import «section 3».MonomialCoordinateSplitting
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def inverseFreeMatrix (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    Matrix (Fin n) (Fin K.freeArity) ℤ :=
  fun i j => integerBasisInverseMatrix E.basis i (K.freeIndex j)

def inverseResidueCoefficient (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) : Fin n → (CanonicalRV.RVSort M)ˣ :=
  integerMonomialMap (fun i j => integerBasisInverseMatrix E.basis i (K.zeroIndex j)) r

/-- Every original RV coordinate in an inverse angular chart is a
residue-dependent coefficient times a free integral monomial. -/
theorem coordinateEquiv_symm_monomial (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) (u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :
    (E.coordinateEquiv K).symm (r,u) = E.inverseResidueCoefficient K r * integerMonomialMap (E.inverseFreeMatrix K) u := by
  funext i
  exact coordinateProductChart_character_split K (integerBasisInverseMatrix E.basis i) r u
end RVAngularCell
end DiamondIntegral.Section3
