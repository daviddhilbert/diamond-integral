import «section 4».GammaIteratedIntegral
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-! Actual finite disjoint partitions give sums of indicator families and
Euler integrals. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFinitePartitions
open GammaOrderLogic GammaIntegerFamilies GammaIndicators GammaIteratedIntegral

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def familyEvaluation (B : Base (M := M)) (n : ℕ) (z : Fin n → Values.Gamma (M := M)) :
    familySubgroup B n →+ ℤ where
  toFun f := f.val z
  map_zero' := rfl
  map_add' _ _ := rfl

theorem indicator_partition {ι : Type} [Fintype ι] (B : Base (M := M)) (n : ℕ)
    (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)
    (C : ι → Set (Fin n → Values.Gamma (M := M))) (hC : ∀ i, GammaDefinable B (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hcover : X = ⋃ i, C i) :
    indicatorFamily B X hX = ∑ i, indicatorFamily B (C i) (hC i) := by
  apply Subtype.ext
  funext z
  have hp : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint C := fun i _ j _ hij => hdisj hij
  have h := Finset.indicator_biUnion_apply Finset.univ C (f := fun _ => (1 : ℤ)) hp z
  have hv := map_sum (familyEvaluation B n z) (fun i => indicatorFamily B (C i) (hC i)) Finset.univ
  change (indicatorFamily B X hX).val z = (familyEvaluation B n z) (∑ i, indicatorFamily B (C i) (hC i))
  rw [hv]
  change (if z ∈ X then (1 : ℤ) else 0) = ∑ i, if z ∈ C i then 1 else 0
  simpa only [Finset.mem_univ, Set.iUnion_true, Set.indicator_apply, hcover] using h

theorem integral_partition {ι : Type} [Fintype ι] (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ)
    (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)
    (C : ι → Set (Fin n → Values.Gamma (M := M))) (hC : ∀ i, GammaDefinable B (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hcover : X = ⋃ i, C i) :
    integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B X hX) =
      ∑ i, integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B (C i) (hC i)) := by
  rw [indicator_partition B n X hX C hC hdisj hcover, map_sum]

end DiamondIntegral.Section4.GammaFinitePartitions
