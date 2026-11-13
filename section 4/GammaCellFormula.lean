import «section 4».GammaCylindricalCells
import «section 4».GammaFinitePartitions

/-! For every supplied actual finite cylindrical cell decomposition, the
constructed geometric integral is the sum of (-1)^dimension. This is a
normalization theorem; existence of a classical cell decomposition and
the topological-dimension identification are not assumed in its proof. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCellFormula
open GammaOrderLogic GammaIndicators GammaIteratedIntegral GammaFinitePartitions GammaCylindricalCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem geometric_partition_formula {ι : Type} [Fintype ι]
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)
    (C : ι → Set (Fin n → Values.Gamma (M := M))) (d : ι → ℕ)
    (hc : ∀ i, Cell B n (C i) (d i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hcover : X = ⋃ i, C i) :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B X hX) =
      ∑ i, (-1 : ℤ) ^ d i := by
  have h := integral_partition h00 hκ hs B hr hγ EulerKind.geometric n X hX C
    (fun i => (hc i).definable) hdisj hcover
  exact h.trans (Finset.sum_congr rfl (fun i _ => geometric_value h00 hκ hs B hr hγ (hc i)))

end DiamondIntegral.Section4.GammaCellFormula
