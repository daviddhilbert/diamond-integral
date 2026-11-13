import «section 3».RVGlobalFreeValues
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Checked data for the angular part of an RV product normal form.
The quotient and rectangle assembly remain separate constructions. -/
structure RVAngularCell (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) where
  residueArity : ℕ
  basis : Module.Basis (Fin n) ℤ (Fin n → ℤ)
  active : Fin residueArity ↪ Fin n
  arity_le : residueArity ≤ n
  finite_values : ((fun x => fun i => rvUnitValueHom (integerMonomialBasisEquiv basis x (active i))) '' A).Finite
  invariant : ∀ x ∈ A, ∀ y : Fin n → (CanonicalRV.RVSort M)ˣ,
    (∀ i, integerMonomialBasisEquiv basis x (active i) = integerMonomialBasisEquiv basis y (active i)) →
    (∀ j, j ∉ Set.range active → rvUnitValueHom (integerMonomialBasisEquiv basis x j) =
      rvUnitValueHom (integerMonomialBasisEquiv basis y j)) → y ∈ A

theorem rvDNFPatternCell_angularCell {I R : Type} (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) :
    Nonempty (RVAngularCell (rvDNFPatternCell D a r p)) := by
  obtain ⟨q,F,hq,hfinite,_⟩ := rvDNFPatternCell_residue_coordinates D a r p
  exact ⟨⟨q,F.bM,F.f,hq,hfinite,fun x hx y ha hf => rvDNFPatternCell_monomial_free_invariant D a r p F x y hx ha hf⟩⟩
end DiamondIntegral.Section3
