import «section 3».LiteralCharacters
import «section 3».RVMonomialBasis
import Mathlib.Data.Set.Finite.Lattice
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def clauseActiveCharacters (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool) : Set (Fin n → ℤ) :=
  ⋃ L : C, literalActiveCharacters L.val a r (b L)

def rvClauseValueCell (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool) :
    Set (Fin n → (CanonicalRV.RVSort M)ˣ) :=
  {x | (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) ∧
    ∀ L : C, literalValueCell L.val a r (b L) x}

theorem clauseActiveCharacters_finite (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool) :
    (clauseActiveCharacters C a r b).Finite :=
  Set.finite_iUnion (fun L => literalActiveCharacters_finite L.val a r (b L))

theorem clauseActiveCharacters_value_finite (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool)
    (hcert : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ C, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L) :
    ∀ e ∈ clauseActiveCharacters C a r b,
      (characterValueImage (rvUnitValueHom (M := M)) (rvClauseValueCell C a r b) e).Finite := by
  intro e he
  obtain ⟨L,he⟩ := Set.mem_iUnion.mp he
  exact literalActiveCharacters_value_finite L.val a r (b L) _
    (fun x hx => hcert x hx.1 L.val L.property) (fun x hx => hx.2 L) e he

theorem rvClauseValueCell_angular_invariant (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool)
    (hcert : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ C, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvClauseValueCell C a r b)
    (hxy : ∀ e ∈ clauseActiveCharacters C a r b, integerCharacter e x = integerCharacter e y)
    (hvalues : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) : y ∈ rvClauseValueCell C a r b := by
  refine ⟨?_,?_⟩
  · intro L hL
    let l : C := ⟨L,hL⟩
    exact (literal_comparison_depends_on_characters L a r (b l) x y
      (fun e he => hxy e (Set.mem_iUnion.mpr ⟨l,he⟩)) hvalues
      (hcert x hx.1 L hL) (hx.2 l)).mp (hx.1 L hL)
  · intro L
    exact (literalValueCell_iff_of_values L.val a r (b L) x y hvalues).mp (hx.2 L)

/-- Every certified value cell has an actual integral monomial basis
whose residue coordinates control all angular membership. -/
theorem rvClauseValueCell_residue_coordinates (C : Finset (RVLiteral I R (Fin n)))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : C → Bool)
    (hcert : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ C, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ C, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L) :
    ∃ q : ℕ, ∃ F : Module.Basis.SmithNormalForm (Submodule.span ℤ (clauseActiveCharacters C a r b)) (Fin n) q,
      q ≤ n ∧
      ((fun x => fun i : Fin q => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (F.f i))) '' rvClauseValueCell C a r b).Finite ∧
      (∀ x ∈ rvClauseValueCell C a r b, ∀ y : Fin n → (CanonicalRV.RVSort M)ˣ,
        (∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i)) →
        (∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) → y ∈ rvClauseValueCell C a r b) := by
  obtain ⟨q,F,hq,hfinite,hdep⟩ := rv_exists_monomial_residue_coordinates (rvClauseValueCell C a r b)
    (clauseActiveCharacters C a r b) (clauseActiveCharacters_value_finite C a r b hcert)
  refine ⟨q,F,hq,hfinite,?_⟩
  intro x hx y hcoord hvalues
  exact rvClauseValueCell_angular_invariant C a r b hcert x y hx
    (fun e he => hdep e (Submodule.subset_span he) x y hcoord) hvalues
end DiamondIntegral.Section3
