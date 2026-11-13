import «section 4».GammaContinuousDecompositionRefinement
import «section 4».GammaConstructedCellEuler

/-! Finite continuous cell decomposition and the usual alternating
cell-dimension Euler formula. Only the rational-affine normal form is
supplied as Section 3 background; continuity refinement, decomposition
and the Euler identity are proved here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousDecomposition
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaContinuousCells GammaContinuousPartitions GammaIndicators GammaIteratedIntegral
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_decomposition (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (affine : Section3GammaAffineInput.Input B)
    (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X) :
    Nonempty (Decomposition B n X) := by
  induction n with
  | zero => exact exists_zero B X
  | succ n ih =>
    obtain ⟨P⟩ := GammaFiniteGraphPartition.exists_boundaryPartition h00 hκ hs B hr hγ X hX
    obtain ⟨Q⟩ := exists_common B affine (endpoint P) (endpoint_definable P)
    let D (label : Label P.size) (j : Q.Index) : Decomposition B n (base X P label ∩ Q.domain j) :=
      Classical.choice (ih _ (GammaRelationLogic.inter_definable_base B _ _
        (base_definable X hX P label) (Q.definable j)))
    exact ⟨GammaContinuousDecompositionRefinement.refine h00 X hX P Q D⟩

variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (affine : Section3GammaAffineInput.Input B)
variable (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)

def decomposition : Decomposition B n X :=
  Classical.choice (exists_decomposition h00 hκ hs B hr hγ affine n X hX)

theorem geometric_sum (D : Decomposition B n X) :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i :=
  GammaConstructedCellEuler.geometric_sum h00 hκ hs B hr hγ n X hX D.toDecomposition

theorem constructed_geometric_sum :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i : Fin (decomposition h00 hκ hs B hr hγ affine n X hX).size,
        (-1 : ℤ) ^ (decomposition h00 hκ hs B hr hγ affine n X hX).dimension i :=
  geometric_sum h00 hκ hs B hr hγ n X hX (decomposition h00 hκ hs B hr hγ affine n X hX)

include h00 hκ hs hr hγ hX in
theorem sum_independent (D E : Decomposition B n X) :
    (∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i) = ∑ j : Fin E.size, (-1 : ℤ) ^ E.dimension j :=
  (geometric_sum h00 hκ hs B hr hγ n X hX D).symm.trans
    (geometric_sum h00 hκ hs B hr hγ n X hX E)

theorem pieces_nonempty (i : Fin (decomposition h00 hκ hs B hr hγ affine n X hX).size) :
    ((decomposition h00 hκ hs B hr hγ affine n X hX).pieces i).Nonempty :=
  ((decomposition h00 hκ hs B hr hγ affine n X hX).continuous_cells i).nonempty

theorem dimensions_bounded (i : Fin (decomposition h00 hκ hs B hr hγ affine n X hX).size) :
    (decomposition h00 hκ hs B hr hγ affine n X hX).dimension i ≤ n :=
  ((decomposition h00 hκ hs B hr hγ affine n X hX).continuous_cells i).dimension_le

end DiamondIntegral.Section4.GammaContinuousDecomposition
