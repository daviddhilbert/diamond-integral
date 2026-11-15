import «section 5».MonomialDecomposition

/-! Explicit GL_n(Z) form of the original-ground monomial decomposition.
The output rows are ordered with the residue block first and the free
block second, using the arity equality in each checked product chart. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

namespace GroundMonomialPiece

def rowOrder (P : GroundMonomialPiece X) : Fin n ≃ Fin n :=
  (finCongr P.arity_eq.symm).trans P.split.coordinates

def orderedBasis (P : GroundMonomialPiece X) : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
  P.cell.basis.reindex P.rowOrder.symm

/-- A matrix with its actual two-sided integral inverse, hence GL_n(Z). -/
def matrix (P : GroundMonomialPiece X) : (Matrix (Fin n) (Fin n) ℤ)ˣ :=
  ⟨integerBasisMatrix P.orderedBasis, integerBasisInverseMatrix P.orderedBasis,
    integerBasis_mul_inverse P.orderedBasis, integerBasisInverse_mul P.orderedBasis⟩

def blockSplit {G : Type} (P : GroundMonomialPiece X) (z : Fin n → G) :
    (Fin P.split.zeroArity → G) × (Fin P.split.freeArity → G) :=
  (fun i => z (Fin.cast P.arity_eq (Fin.castAdd P.split.freeArity i)),
   fun i => z (Fin.cast P.arity_eq (Fin.natAdd P.split.zeroArity i)))

theorem rowOrder_fixed (P : GroundMonomialPiece X) (i : Fin P.split.zeroArity) :
    P.rowOrder (Fin.cast P.arity_eq (Fin.castAdd P.split.freeArity i)) = P.split.zeroIndex i := by
  simp [rowOrder, Section2.ZeroFaceChart.zeroIndex]

theorem rowOrder_free (P : GroundMonomialPiece X) (i : Fin P.split.freeArity) :
    P.rowOrder (Fin.cast P.arity_eq (Fin.natAdd P.split.zeroArity i)) = P.split.freeIndex i := by
  simp [rowOrder, Section2.ZeroFaceChart.freeIndex]

theorem matrix_blockSplit (P : GroundMonomialPiece X)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    P.blockSplit (integerMonomialMap P.matrix.val x) = P.cell.coordinateEquiv P.split x := by
  apply Prod.ext
  · funext i
    change integerMonomialMap (integerBasisMatrix P.orderedBasis) x
      (Fin.cast P.arity_eq (Fin.castAdd P.split.freeArity i)) =
      integerMonomialMap (integerBasisMatrix P.cell.basis) x (P.split.zeroIndex i)
    simp only [integerMonomialMap, integerBasisMatrix, orderedBasis, Module.Basis.reindex_apply,
      Equiv.symm_symm, rowOrder_fixed]
  · funext i
    change integerMonomialMap (integerBasisMatrix P.orderedBasis) x
      (Fin.cast P.arity_eq (Fin.natAdd P.split.zeroArity i)) =
      integerMonomialMap (integerBasisMatrix P.cell.basis) x (P.split.freeIndex i)
    simp only [integerMonomialMap, integerBasisMatrix, orderedBasis, Module.Basis.reindex_apply,
      Equiv.symm_symm, rowOrder_free]

/-- Literal image under the integer unimodular matrix, with the first
residue coordinates and last free coordinates in their standard order. -/
theorem matrix_image (P : GroundMonomialPiece X) :
    integerMonomialMap P.matrix.val '' P.source.carrier =
      P.blockSplit ⁻¹' (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)).carrier := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change P.blockSplit (integerMonomialMap P.matrix.val x) ∈
      (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)).carrier
    rw [P.matrix_blockSplit]
    exact P.coordinate_image ▸ ⟨x, hx, rfl⟩
  · intro hz
    obtain ⟨x, hx⟩ := (integerMonomialBasisEquiv (G := (CanonicalRV.RVSort M)ˣ) P.orderedBasis).surjective z
    change integerMonomialMap P.matrix.val x = z at hx
    subst z
    change P.blockSplit (integerMonomialMap P.matrix.val x) ∈
      (P.residue.prod (gammaGroundRVUnitGammaPreimage P.gamma)).carrier at hz
    rw [P.matrix_blockSplit] at hz
    obtain ⟨y, hy, he⟩ := P.coordinate_image.symm ▸ hz
    have hyx : y = x := (P.cell.coordinateEquiv P.split).injective he
    exact ⟨x, hyx ▸ hy, rfl⟩

end GroundMonomialPiece

/-- Lemma 5.12 for actual nonzero RV-definable sets: original-ground
value partition, nonempty singleton-value residue factors, nonempty Gamma
factors, and explicit GL_n(Z) matrices in standard block order. -/
theorem monomial_decomposition_5_12 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    ∃ N : ℕ, ∃ C : Fin N → GroundMonomialPiece X,
      (∀ i j, i ≠ j → Disjoint (C i).values.carrier (C j).values.carrier) ∧
      (∀ γ, γ ∈ rvUnitTupleValues '' X.carrier ↔ ∃ j, γ ∈ (C j).values.carrier) ∧
      (∀ j, integerMonomialMap (C j).matrix.val '' (C j).source.carrier =
        (C j).blockSplit ⁻¹'
          ((C j).residue.prod (gammaGroundRVUnitGammaPreimage (C j).gamma)).carrier) := by
  obtain ⟨N, C, hd, hc⟩ := ground_global_monomial_decomposition hκ hs h00 hsmall hγsmall hΓ X
  exact ⟨N, C, hd, hc, fun j => (C j).matrix_image⟩

end DiamondIntegral.Section5
