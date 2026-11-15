import «section 5».OriginalSortedPredicates
import IntegrationSection6.GammaFamilyValidity

/-! Full finite disjoint coverage has a genuine original-base validity
locus, including exclusion of overlaps away from the prescribed source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem original_finite_partition_validity_definable
    (B : Base (M := M)) {p n N : ℕ} (sp : Fin p → SortTag) (sx : Fin n → SortTag)
    (D : Set (Fin (p+n) → M)) (C : Fin N → Set (Fin (p+n) → M))
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hC : ∀ i, DefinableOverBase B (Fin.append sp sx) (C i)) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      (∀ x : Fin n → M, Fin.append z x ∈ D ↔ ∃ i, Fin.append z x ∈ C i) ∧
      ∀ i j, i ≠ j → ∀ x : Fin n → M,
        ¬ (Fin.append z x ∈ C i ∧ Fin.append z x ∈ C j)} := by
  have hUnion := DefinableOverBase.finite_iUnion Finset.univ C (fun i _ => hC i)
  have hcov := gamma_family_row_eq_definable sp sx hD hUnion
  have hcov' : OriginalSortedPredicate B sp (fun z =>
      ∀ x : Fin n → M, Fin.append z x ∈ D ↔ ∃ i, Fin.append z x ∈ C i) := by
    unfold OriginalSortedPredicate
    simpa only [sortedUniverse, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and] using hcov
  have hdis (i j : Fin N) : OriginalSortedPredicate B sp (fun z =>
      i ≠ j → ∀ x : Fin n → M, ¬ (Fin.append z x ∈ C i ∧ Fin.append z x ∈ C j)) := by
    by_cases hij : i = j
    · simpa only [hij, ne_eq, not_true_eq_false, false_implies, implies_true] using
        (OriginalSortedPredicate.truth (B := B) (s := sp))
    · have h := gamma_family_row_subset_definable sp sx ((hC i).inter (hC j))
        (DefinableOverBase.empty B (Fin.append sp sx))
      unfold OriginalSortedPredicate
      simpa only [sortedUniverse, Set.mem_ofPred_eq, ne_eq, hij, Set.mem_inter_iff, Set.notMem_empty, imp_false, not_false_eq_true,
        true_implies] using h
  exact hcov'.conj (OriginalSortedPredicate.finite_all (fun i =>
    OriginalSortedPredicate.finite_all (fun j => hdis i j)))

end DiamondIntegral.Section5
