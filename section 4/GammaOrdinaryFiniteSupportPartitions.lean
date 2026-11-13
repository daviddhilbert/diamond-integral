import «section 4».GammaOrdinaryFiniteRing
import «section 4».GammaFiniteRVPartitions

/-! Partition additivity in the separate ordinary finite Gamma ring.
Every piece retains a proved finite support. The proof forgets volume
from constant-volume representatives, without assuming that the map
from finite to full Gamma is injective. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteSupportPartitions
open GammaOrdinaryCharts GammaOrdinaryFiniteCharts GammaOrdinaryFiniteRing GammaOrderLogic
open GammaRVFinitePartitions (support)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def restrict {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (hi : I ⊆ a.support) : FiniteChart B n := ⟨⟨I, hI⟩, a.finite_support.subset hi⟩

theorem class_partition {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ} (a : FiniteChart B n)
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i))
    (hi : ∀ i, I i ⊆ a.support) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j))
    (hc : support s I = a.support) :
    objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i) (hi i)) := by
  have h := congrArg (forget B) (GammaFiniteRVPartitions.class_partition s
    (GammaOrdinaryFiniteCharts.toWeighted a) I hI hi hd hc)
  simp only [map_sum, forget_class] at h
  change objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i) (hi i)) at h
  exact h

end DiamondIntegral.Section4.GammaOrdinaryFiniteSupportPartitions
