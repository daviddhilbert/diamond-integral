import «section 3».RVGlobalValuePatterns
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

theorem rvDNFPatternCell_monomial_free_invariant (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D)
    {q : ℕ} (F : Module.Basis.SmithNormalForm (Submodule.span ℤ (rvDNFPatternCharacters D a r p)) (Fin n) q)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvDNFPatternCell D a r p)
    (hactive : ∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i))
    (hfree : ∀ j, j ∉ Set.range F.f → rvUnitValueHom (integerMonomialBasisEquiv F.bM x j) =
      rvUnitValueHom (integerMonomialBasisEquiv F.bM y j)) : y ∈ rvDNFPatternCell D a r p := by
  exact rvDNFPatternCell_angular_invariant D a r p x y hx
    (fun e he => integerCharacter_depends_on_smith_coordinates F e (Submodule.subset_span he) x y hactive)
    (integerMonomialBasis_value_eq_of_active_and_free (rvUnitValueHom (M := M)) F x y hactive hfree)

theorem rvDNFPatternCell_chart_invariant (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D)
    {q : ℕ} (F : Module.Basis.SmithNormalForm (Submodule.span ℤ (rvDNFPatternCharacters D a r p)) (Fin n) q)
    (K : Section2.ZeroFaceChart (Set.range F.f))
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvDNFPatternCell D a r p)
    (hactive : ∀ i, integerMonomialBasisEquiv F.bM x (K.zeroIndex i) = integerMonomialBasisEquiv F.bM y (K.zeroIndex i))
    (hfree : ∀ i, rvUnitValueHom (integerMonomialBasisEquiv F.bM x (K.freeIndex i)) =
      rvUnitValueHom (integerMonomialBasisEquiv F.bM y (K.freeIndex i))) : y ∈ rvDNFPatternCell D a r p := by
  apply rvDNFPatternCell_monomial_free_invariant D a r p F x y hx
  · intro i
    obtain ⟨j,hj⟩ := coordinateProductChart_fixed_cover K (F.f i) (Set.mem_range_self i)
    rw [hj]
    exact hactive j
  · intro j hj
    obtain ⟨i,rfl⟩ := coordinateProductChart_free_cover K j hj
    exact hfree i
end DiamondIntegral.Section3
