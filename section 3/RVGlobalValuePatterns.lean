import «section 3».PatternLiteralCharacters
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

def rvDNFLiterals (D : LiteralDNF I R (Fin n)) : Finset (RVLiteral I R (Fin n)) := D.flatten.toFinset

abbrev RVDNFGlobalPattern (D : LiteralDNF I R (Fin n)) :=
  (L : rvDNFLiterals D) → LiteralValuePattern L.val

instance rvDNFGlobalPattern_finite (D : LiteralDNF I R (Fin n)) : Finite (RVDNFGlobalPattern D) := by
  unfold RVDNFGlobalPattern
  infer_instance

def rvDNFPatternCell (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) :
    Set (Fin n → (CanonicalRV.RVSort M)ˣ) :=
  {x | PolarityDNF.holds (RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M))) D ∧
    ∀ L : rvDNFLiterals D, literalPatternCell L.val a r (p L) x}

def rvDNFPatternCharacters (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) : Set (Fin n → ℤ) :=
  ⋃ L : rvDNFLiterals D, literalPatternCharacters L.val a r (p L)

theorem rvDNFLiterals_mem {D : LiteralDNF I R (Fin n)} {C : List (RVLiteral I R (Fin n))}
    (hC : C ∈ D) {L : RVLiteral I R (Fin n)} (hL : L ∈ C) : L ∈ rvDNFLiterals D :=
  List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨C,hC,hL⟩)

theorem rvDNFPatternCells_cover (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    PolarityDNF.holds (RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M))) D ↔
      ∃ p : RVDNFGlobalPattern D, x ∈ rvDNFPatternCell D a r p := by
  exact ⟨fun hx => ⟨fun L => literalPattern L.val a r x,hx,fun L => literalPatternCell_own L.val a r x⟩,
    fun ⟨p,hx⟩ => hx.1⟩

theorem rvDNFPatternCells_disjoint (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (p q : RVDNFGlobalPattern D) (hpq : p ≠ q) :
    Disjoint (rvDNFPatternCell D a r p) (rvDNFPatternCell D a r q) := by
  apply Set.disjoint_left.mpr
  intro x hx hq
  apply hpq
  funext L
  exact literalPatternCell_unique L.val a r x (p L) (q L) (hx.2 L) (hq.2 L)

theorem rvDNFPatternCells_finite (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    (Set.range (rvDNFPatternCell D a r)).Finite := Set.finite_range _

theorem rvDNFPatternCharacters_finite (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) :
    (rvDNFPatternCharacters D a r p).Finite :=
  Set.finite_iUnion (fun L => literalPatternCharacters_finite L.val a r (p L))

theorem rvDNFPatternCharacters_value_finite (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) :
    ∀ e ∈ rvDNFPatternCharacters D a r p,
      (characterValueImage (rvUnitValueHom (M := M)) (rvDNFPatternCell D a r p) e).Finite := by
  intro e he
  obtain ⟨L,he⟩ := Set.mem_iUnion.mp he
  exact literalPatternCharacters_value_finite L.val a r (p L) _ (fun x hx => hx.2 L) e he

/-- Each global value pattern is angularly invariant for arbitrary DNF
truth values, while all original guards remain literal parts of the DNF. -/
theorem rvDNFPatternCell_angular_invariant (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hx : x ∈ rvDNFPatternCell D a r p)
    (hxy : ∀ e ∈ rvDNFPatternCharacters D a r p, integerCharacter e x = integerCharacter e y)
    (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) : y ∈ rvDNFPatternCell D a r p := by
  refine ⟨?_,?_⟩
  · obtain ⟨C,hC,hcomp⟩ := hx.1
    refine ⟨C,hC,?_⟩
    intro L hL
    let l : rvDNFLiterals D := ⟨L,rvDNFLiterals_mem hC hL⟩
    exact (literal_comparison_depends_on_pattern_characters L a r (p l) x y
      (fun e he => hxy e (Set.mem_iUnion.mpr ⟨l,he⟩)) hv (hx.2 l)).mp (hcomp L hL)
  · intro L
    exact (literalPatternCell_iff_of_values L.val a r (p L) x y hv).mp (hx.2 L)

/-- A finite disjoint global-value partition has residue coordinates in
each cell; no isolated-type assumption or HK statement is used. -/
theorem rvDNFPatternCell_residue_coordinates (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : RVDNFGlobalPattern D) :
    ∃ q : ℕ, ∃ F : Module.Basis.SmithNormalForm (Submodule.span ℤ (rvDNFPatternCharacters D a r p)) (Fin n) q,
      q ≤ n ∧
      ((fun x => fun i : Fin q => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (F.f i))) '' rvDNFPatternCell D a r p).Finite ∧
      (∀ x ∈ rvDNFPatternCell D a r p, ∀ y : Fin n → (CanonicalRV.RVSort M)ˣ,
        (∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i)) →
        (∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) → y ∈ rvDNFPatternCell D a r p) := by
  obtain ⟨q,F,hq,hfinite,hdep⟩ := rv_exists_monomial_residue_coordinates (rvDNFPatternCell D a r p)
    (rvDNFPatternCharacters D a r p) (rvDNFPatternCharacters_value_finite D a r p)
  refine ⟨q,F,hq,hfinite,?_⟩
  intro x hx y hcoord hv
  exact rvDNFPatternCell_angular_invariant D a r p x y hx
    (fun e he => hdep e (Submodule.subset_span he) x y hcoord) hv
end DiamondIntegral.Section3
