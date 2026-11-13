import «section 3».RVAngularOutputMonomials
import «section 3».RVAngularGraphRigidity
import «section 3».RVAngularCellFullFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- If both input and output projections are injective on a square graph
chart, its induced integral output matrix is unimodular. -/
theorem rvAngularGraph_output_matrix_unimodular (h00 : M ⊨ Axioms.ACVF00)
    {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)} (E : RVAngularCell A)
    (K : Section2.ZeroFaceChart (Set.range E.active)) (I O : Fin K.freeArity → Fin n)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ A)
    (hI : Set.InjOn (fun z => z ∘ I) A) (hO : Set.InjOn (fun z => z ∘ O) A) :
    IsUnit (E.outputMonomialMatrix K I O).det := by
  let r := (E.coordinateEquiv K x).1
  let δ := rvUnitTupleValues (E.coordinateEquiv K x).2
  have hfull := fun u hu => E.coordinate_full_fibre K x hx u hu
  have hi := rvAngularGraph_free_block_unimodular h00 E K I r δ hfull hI
  have ho := rvAngularGraph_free_block_unimodular h00 E K O r δ hfull hO
  let P := (E.inverseFreeMatrix K).submatrix I id
  have hp : IsUnit (P⁻¹).det := Matrix.isUnit_det_of_right_inverse (Matrix.nonsing_inv_mul P hi)
  rw [RVAngularCell.outputMonomialMatrix,Matrix.det_mul]
  exact ho.mul hp
end DiamondIntegral.Section3
