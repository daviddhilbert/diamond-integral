import «section 3».UnimodularMonomialFibres
import «section 3».RVAngularOutputMonomials
import «section 3».RVAngularCellFullFibres
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

theorem input_value_fibre_solve (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (I : Fin K.freeArity → Fin n) (hI : IsUnit ((E.inverseFreeMatrix K).submatrix I id).det)
    (r : Fin K.zeroArity → (CanonicalRV.RVSort M)ˣ) (u y : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ)
    (hy : rvUnitTupleValues y = rvUnitTupleValues ((E.coordinateEquiv K).symm (r,u) ∘ I)) :
    ∃ v, rvUnitTupleValues v = rvUnitTupleValues u ∧ (E.coordinateEquiv K).symm (r,v) ∘ I = y := by
  let F := (E.inverseFreeMatrix K).submatrix I id
  let c := E.inverseResidueCoefficient K r ∘ I
  have he (v : Fin K.freeArity → (CanonicalRV.RVSort M)ˣ) :
      (E.coordinateEquiv K).symm (r,v) ∘ I = c * integerMonomialMap F v :=
    congrArg (fun z => z ∘ I) (E.coordinateEquiv_symm_monomial K r v)
  obtain ⟨v,hv,hvy⟩ := affineMonomial_full_value_fibre_solve (rvUnitValueHom (M := M)) F hI c u y
    (hy.trans (congrArg rvUnitTupleValues (he u)))
  exact ⟨v,hv,(he v).trans hvy⟩

/-- A square graph chart determines its output on the entire original
input value fibre, even across the other cells of the surrounding graph. -/
theorem output_on_value_fibre (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (I : Fin K.freeArity → Fin n) (O : Fin l → Fin n)
    (hI : IsUnit ((E.inverseFreeMatrix K).submatrix I id).det)
    (T : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (hAT : A ⊆ T)
    (hinj : Set.InjOn (fun z => z ∘ I) T)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ A)
    (y : Fin n → (CanonicalRV.RVSort M)ˣ) (hy : y ∈ T)
    (hxy : rvUnitTupleValues (y ∘ I) = rvUnitTupleValues (x ∘ I)) :
    y ∘ O = integerMonomialMap (E.outputCoefficientMatrix K I O) (E.coordinateEquiv K x).1 *
      integerMonomialMap (E.outputMonomialMatrix K I O) (y ∘ I) := by
  let r := (E.coordinateEquiv K x).1
  let u := (E.coordinateEquiv K x).2
  have hxu : (E.coordinateEquiv K).symm (r,u) = x := (E.coordinateEquiv K).symm_apply_apply x
  have hxy' : rvUnitTupleValues (y ∘ I) = rvUnitTupleValues ((E.coordinateEquiv K).symm (r,u) ∘ I) := by
    rw [hxu]
    exact hxy
  obtain ⟨v,hv,hvI⟩ := E.input_value_fibre_solve K I hI r u (y ∘ I) hxy'
  have hz : (E.coordinateEquiv K).symm (r,v) ∈ A := E.coordinate_full_fibre K x hx v hv
  have he : (E.coordinateEquiv K).symm (r,v) = y := hinj (hAT hz) hy hvI
  rw [← he]
  exact E.coordinate_output_monomial K I O hI r v
end RVAngularCell
end DiamondIntegral.Section3
