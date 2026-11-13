import «section 3».IntegerMonomialElimination
import «section 3».RVAngularInverseMonomials
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n l : ℕ}
namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def inverseResidueMatrix (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    Matrix (Fin n) (Fin K.zeroArity) ℤ := fun i j => integerBasisInverseMatrix E.basis i (K.zeroIndex j)

def outputMonomialMatrix (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (I : Fin K.freeArity → Fin n) (O : Fin l → Fin n) : Matrix (Fin l) (Fin K.freeArity) ℤ :=
  (E.inverseFreeMatrix K).submatrix O id * ((E.inverseFreeMatrix K).submatrix I id)⁻¹

def outputCoefficientMatrix (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (I : Fin K.freeArity → Fin n) (O : Fin l → Fin n) : Matrix (Fin l) (Fin K.zeroArity) ℤ :=
  (E.inverseResidueMatrix K).submatrix O id - E.outputMonomialMatrix K I O * (E.inverseResidueMatrix K).submatrix I id

/-- An invertible integral input block makes the graph output an
integral monomial in the original inputs, with an explicit residue coefficient. -/
theorem coordinate_output_monomial (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (I : Fin K.freeArity → Fin n) (O : Fin l → Fin n)
    (hI : IsUnit ((E.inverseFreeMatrix K).submatrix I id).det)
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) (u : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :
    (E.coordinateEquiv K).symm (r,u) ∘ O = integerMonomialMap (E.outputCoefficientMatrix K I O) r *
      integerMonomialMap (E.outputMonomialMatrix K I O) ((E.coordinateEquiv K).symm (r,u) ∘ I) := by
  simp only [E.coordinateEquiv_symm_monomial K r u]
  exact integerMonomialMap_eliminate_coefficients ((E.inverseFreeMatrix K).submatrix I id) hI
    ((E.inverseFreeMatrix K).submatrix O id) ((E.inverseResidueMatrix K).submatrix I id)
    ((E.inverseResidueMatrix K).submatrix O id) r u
end RVAngularCell
end DiamondIntegral.Section3
