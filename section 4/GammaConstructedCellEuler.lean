import «section 4».GammaCylindricalDecompositionExistence
import «section 4».GammaCylindricalCellGeometry

/-! A constructed finite actual cylindrical decomposition for every
definable Gamma set, and its geometric Euler sum. All pieces are nonempty,
their dimensions are bounded by ambient arity, and the alternating sum is
independent of the chosen cylindrical decomposition. Continuous classical
cells and topological dimension are not asserted here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaConstructedCellEuler
open GammaOrderLogic GammaCylindricalDecompositionData GammaCylindricalDecompositionExistence
open GammaIndicators GammaIteratedIntegral
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)

def decomposition : Decomposition B n X := Classical.choice (exists_decomposition h00 hκ hs B hr hγ n X hX)

theorem geometric_sum (D : Decomposition B n X) :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i :=
  GammaCellFormula.geometric_partition_formula h00 hκ hs B hr hγ n X hX D.pieces D.dimension D.cells D.disjoint D.cover

theorem constructed_geometric_sum :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i : Fin (decomposition h00 hκ hs B hr hγ n X hX).size,
        (-1 : ℤ) ^ (decomposition h00 hκ hs B hr hγ n X hX).dimension i :=
  geometric_sum h00 hκ hs B hr hγ n X hX (decomposition h00 hκ hs B hr hγ n X hX)

include h00 hκ hs hr hγ hX in
theorem sum_independent (D E : Decomposition B n X) :
    (∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i) = ∑ j : Fin E.size, (-1 : ℤ) ^ E.dimension j :=
  (geometric_sum h00 hκ hs B hr hγ n X hX D).symm.trans (geometric_sum h00 hκ hs B hr hγ n X hX E)

theorem pieces_nonempty (i : Fin (decomposition h00 hκ hs B hr hγ n X hX).size) :
    ((decomposition h00 hκ hs B hr hγ n X hX).pieces i).Nonempty :=
  GammaCylindricalCellGeometry.nonempty ((decomposition h00 hκ hs B hr hγ n X hX).cells i)

theorem dimensions_bounded (i : Fin (decomposition h00 hκ hs B hr hγ n X hX).size) :
    (decomposition h00 hκ hs B hr hγ n X hX).dimension i ≤ n :=
  GammaCylindricalCellGeometry.dimension_le ((decomposition h00 hκ hs B hr hγ n X hX).cells i)

end DiamondIntegral.Section4.GammaConstructedCellEuler
