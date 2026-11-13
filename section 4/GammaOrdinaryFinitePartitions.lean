import «section 4».GammaOrdinaryRing
import «section 4».GammaRVFinitePartitions

/-! Finite partitions of ordinary Gamma charts. The measured partition
identity is transported through the actual forgetful map using constant
volume representatives; no measured lift of an ordinary isomorphism is
asserted. Formal finite labels add no Gamma coordinates. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFinitePartitions
open GammaOrdinaryCharts GammaOrdinaryRing GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev support := @GammaRVFinitePartitions.support
abbrev support_definable := @GammaRVFinitePartitions.support_definable

def restrict {B : Base (M := M)} {n : ℕ} (_a : Chart B n)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) : Chart B n := ofSet B n I hI

theorem class_partition {B : Base (M := M)} {ι : Type*} (s : Finset ι) {n : ℕ} (a : Chart B n)
    (I : ι → Set (Fin n → Values.Gamma (M := M))) (hI : ∀ i, GammaDefinable B (I i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (I i) (I j)) (hc : support s I = a.support) :
    objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i)) := by
  have h := congrArg (forget B) (GammaRVFinitePartitions.class_partition s (toWeighted a) I hI hd hc)
  simp only [map_sum, forget_class] at h
  change objectClass a = ∑ i ∈ s, objectClass (restrict a (I i) (hI i)) at h
  exact h

end DiamondIntegral.Section4.GammaOrdinaryFinitePartitions
