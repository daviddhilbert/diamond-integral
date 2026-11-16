import «section 6».MeasuredRVPermutations
import Section4.EarlierRVInputs
import Mathlib.Order.Minimal

/-! A finite generating tuple admits a one-coordinate exchange with any
nonloop in its closure. A minimal finite support proves the exchange;
no independence assumption on the whole tuple is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6

theorem exists_generating_tuple_exchange {E : Type*} (N : Matroid E) {n : ℕ}
    (a : Fin n → E) (b : E) (ha : Set.range a ⊆ N.E)
    (hb : b ∈ N.closure (Set.range a)) (hb0 : b ∉ N.closure ∅) :
    ∃ i : Fin n, N.closure (Set.range (Function.update a i b)) = N.closure (Set.range a) := by
  let P (I : Finset (Fin n)) : Prop := b ∈ N.closure (a '' (I : Set (Fin n)))
  obtain ⟨I,hI⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card
    ⟨Finset.univ,by simpa only [P,Finset.coe_univ,Set.image_univ] using hb⟩
  have hne : I.Nonempty := by
    by_contra h
    have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h := hI.prop
    simp only [P,he,Finset.coe_empty,Set.image_empty] at h
    exact hb0 h
  obtain ⟨i,hi⟩ := hne
  have hNo : b ∉ N.closure (a '' (I.erase i : Set (Fin n))) := by
    intro h
    have hlt := Finset.card_erase_lt_of_mem hi
    exact (not_le_of_gt hlt) (hI.le_of_le h (Nat.le_of_lt hlt))
  have hSet : (I : Set (Fin n)) = insert i (I.erase i : Set (Fin n)) := by
    simpa only [Finset.coe_insert] using
      congrArg (fun J : Finset (Fin n) => (J : Set (Fin n))) (Finset.insert_erase hi).symm
  have hYes : b ∈ N.closure (insert (a i) (a '' (I.erase i : Set (Fin n)))) := by
    have h := hI.prop
    change b ∈ N.closure (a '' (I : Set (Fin n))) at h
    rwa [hSet,Set.image_insert_eq] at h
  have hEx := N.mem_closure_insert hNo hYes
  let c := Function.update a i b
  have hbC : b ∈ Set.range c := ⟨i,Function.update_self i b a⟩
  have hRest : a '' (I.erase i : Set (Fin n)) ⊆ Set.range c := by
    rintro z ⟨k,hk,rfl⟩
    exact ⟨k,Function.update_of_ne (Finset.mem_erase.mp hk).1 b a⟩
  have hExC : a i ∈ N.closure (Set.range c) :=
    N.closure_subset_closure (Set.insert_subset hbC hRest) hEx
  refine ⟨i,Set.Subset.antisymm ?_ ?_⟩
  · apply N.closure_subset_closure_of_subset_closure
    rintro z ⟨k,rfl⟩
    by_cases hk : k = i
    · subst k
      simpa only [c,Function.update_self] using hb
    · rw [Function.update_of_ne hk]
      exact N.mem_closure_of_mem' ⟨k,rfl⟩ (ha ⟨k,rfl⟩)
  · apply N.closure_subset_closure_of_subset_closure
    rintro z ⟨k,rfl⟩
    by_cases hk : k = i
    · subst k
      exact hExC
    · have hmem : a k ∈ Set.range c := ⟨k,Function.update_of_ne hk b a⟩
      exact N.mem_closure_of_mem' hmem (ha ⟨k,rfl⟩)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rvParameterNames_range {n : ℕ} (a : Fin n → RVInfinity M) :
    rvParameterNames (Set.range a) = Set.range (rvValues a) := by
  ext x
  constructor
  · rintro ⟨t,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨a i,⟨i,rfl⟩,rfl⟩

theorem exists_rv_generating_tuple_exchange (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n : ℕ} (a : Fin n → RVInfinity M) (b : RVInfinity M)
    (hb : AlgebraicAt (S ∪ Set.range (rvValues a)) .rv b.val) (hb0 : ¬ AlgebraicAt S .rv b.val) :
    ∃ i : Fin n,
      (rvAlgebraicMatroid hc hex S).closure (Set.range (Function.update a i b)) =
        (rvAlgebraicMatroid hc hex S).closure (Set.range a) := by
  apply exists_generating_tuple_exchange (rvAlgebraicMatroid hc hex S) a b
    (by change Set.range a ⊆ Set.univ; exact Set.subset_univ _)
  · rw [rvAlgebraicMatroid_closure]
    change AlgebraicAt (S ∪ rvParameterNames (Set.range a)) .rv b.val
    simpa only [rvParameterNames_range] using hb
  · rw [rvAlgebraicMatroid_closure]
    change ¬ AlgebraicAt (S ∪ rvParameterNames ∅) .rv b.val
    simpa only [rvParameterNames,Set.image_empty,Set.union_empty] using hb0

end DiamondIntegral.Section6
