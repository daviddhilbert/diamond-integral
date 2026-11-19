import «section 4».GammaContinuousDecomposition
import «section 4».Section3GammaAffineDischarge

/-! Remark 4.2 without the multivariate Gamma rational-affine input: that
input is the theorem `Section3GammaAffineDischarge.input`, proved from RV
quantifier elimination over the same base with no further hypotheses. The
statements are otherwise those of `GammaContinuousPartitions` and
`GammaContinuousDecomposition`, which are unchanged.

`GammaContinuousDecomposition.geometric_sum` and `.sum_independent`
quantify over given decompositions and never took the input; it entered
only through the existence of a decomposition. The discharged forms below
therefore record existence, the constructed Euler sum, and the combined
Euler-characteristic statement. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousPartitions
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_partition_discharged (B : Base (M := M))
    {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) : Nonempty (Partition B n T) :=
  exists_partition B (Section3GammaAffineDischarge.input B) T hT

theorem exists_common_discharged (B : Base (M := M))
    {n N : ℕ} (T : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : ∀ j, MapDefinable B (T j)) : Nonempty (CommonCover B n N T) :=
  exists_common B (Section3GammaAffineDischarge.input B) T hT

end DiamondIntegral.Section4.GammaContinuousPartitions

namespace DiamondIntegral.Section4.GammaContinuousDecomposition
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaContinuousCells GammaContinuousPartitions GammaIndicators GammaIteratedIntegral
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_decomposition_discharged (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X) :
    Nonempty (Decomposition B n X) :=
  exists_decomposition h00 hκ hs B hr hγ (Section3GammaAffineDischarge.input B) n X hX

variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)

/-- The constructed continuous cell decomposition, with the input discharged. -/
def decompositionDischarged : Decomposition B n X :=
  decomposition h00 hκ hs B hr hγ (Section3GammaAffineDischarge.input B) n X hX

theorem constructed_geometric_sum_discharged :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i : Fin (decompositionDischarged h00 hκ hs B hr hγ n X hX).size,
        (-1 : ℤ) ^ (decompositionDischarged h00 hκ hs B hr hγ n X hX).dimension i :=
  constructed_geometric_sum h00 hκ hs B hr hγ (Section3GammaAffineDischarge.input B) n X hX

theorem geometric_sum_discharged :
    ∃ D : Decomposition B n X,
      integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
        ∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i :=
  ⟨decompositionDischarged h00 hκ hs B hr hγ n X hX,
    geometric_sum h00 hκ hs B hr hγ n X hX _⟩

/-- Remark 4.2's Euler characteristic: a continuous cell decomposition
exists, its signed cell count is the geometric Gamma integral, and every
other decomposition has the same signed cell count. -/
theorem euler_characteristic_discharged :
    ∃ D : Decomposition B n X,
      integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
        ∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i ∧
      ∀ E : Decomposition B n X,
        (∑ j : Fin E.size, (-1 : ℤ) ^ E.dimension j) = ∑ i : Fin D.size, (-1 : ℤ) ^ D.dimension i :=
  ⟨decompositionDischarged h00 hκ hs B hr hγ n X hX,
    geometric_sum h00 hκ hs B hr hγ n X hX _,
    fun E => sum_independent h00 hκ hs B hr hγ n X hX E _⟩

theorem pieces_nonempty_discharged
    (i : Fin (decompositionDischarged h00 hκ hs B hr hγ n X hX).size) :
    ((decompositionDischarged h00 hκ hs B hr hγ n X hX).pieces i).Nonempty :=
  pieces_nonempty h00 hκ hs B hr hγ (Section3GammaAffineDischarge.input B) n X hX i

theorem dimensions_bounded_discharged
    (i : Fin (decompositionDischarged h00 hκ hs B hr hγ n X hX).size) :
    (decompositionDischarged h00 hκ hs B hr hγ n X hX).dimension i ≤ n :=
  dimensions_bounded h00 hκ hs B hr hγ (Section3GammaAffineDischarge.input B) n X hX i

end DiamondIntegral.Section4.GammaContinuousDecomposition
