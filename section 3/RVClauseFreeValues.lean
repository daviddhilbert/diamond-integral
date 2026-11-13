import «section 3».RVClauseCharacters
import «section 3».MonomialBasisValues
import «section 3».CoordinateProductChart
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvClauseValueCell_monomial_free_invariant (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool)
    (hcert : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ C, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L)
    {q : ℕ} (F : Module.Basis.SmithNormalForm (Submodule.span ℤ (clauseActiveCharacters C a r b)) (Fin n) q)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvClauseValueCell C a r b)
    (hactive : ∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i))
    (hfree : ∀ j, j ∉ Set.range F.f → rvUnitValueHom (integerMonomialBasisEquiv F.bM x j) =
      rvUnitValueHom (integerMonomialBasisEquiv F.bM y j)) : y ∈ rvClauseValueCell C a r b := by
  exact rvClauseValueCell_angular_invariant C a r b hcert x y hx
    (fun e he => integerCharacter_depends_on_smith_coordinates F e (Submodule.subset_span he) x y hactive)
    (integerMonomialBasis_value_eq_of_active_and_free (rvUnitValueHom (M := M)) F x y hactive hfree)

theorem rvClauseValueCell_chart_invariant (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool)
    (hcert : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ C, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L)
    {q : ℕ} (F : Module.Basis.SmithNormalForm (Submodule.span ℤ (clauseActiveCharacters C a r b)) (Fin n) q)
    (K : Section2.ZeroFaceChart (Set.range F.f))
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvClauseValueCell C a r b)
    (hactive : ∀ i, integerMonomialBasisEquiv F.bM x (K.zeroIndex i) = integerMonomialBasisEquiv F.bM y (K.zeroIndex i))
    (hfree : ∀ i, rvUnitValueHom (integerMonomialBasisEquiv F.bM x (K.freeIndex i)) =
      rvUnitValueHom (integerMonomialBasisEquiv F.bM y (K.freeIndex i))) : y ∈ rvClauseValueCell C a r b := by
  apply rvClauseValueCell_monomial_free_invariant C a r b hcert F x y hx
  · intro i
    obtain ⟨j,hj⟩ := coordinateProductChart_fixed_cover K (F.f i) (Set.mem_range_self i)
    rw [hj]
    exact hactive j
  · intro j hj
    obtain ⟨i,rfl⟩ := coordinateProductChart_free_cover K j hj
    exact hfree i
end DiamondIntegral.Section3
