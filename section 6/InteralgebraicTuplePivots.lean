import «section 6».GeneratingTupleExchange

/-! Two positive-length generating tuples of the same algebraic closure
have a source coordinate that can be replaced by a target coordinate
without changing that closure. This includes the rank-zero case. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6

theorem exists_interalgebraic_tuple_pivot {E : Type*} (N : Matroid E) {n : ℕ} (hn : 0 < n)
    (a b : Fin n → E) (ha : Set.range a ⊆ N.E) (hb : Set.range b ⊆ N.E)
    (he : N.closure (Set.range a) = N.closure (Set.range b)) :
    ∃ i j : Fin n, N.closure (Set.range (Function.update a i (b j))) = N.closure (Set.range a) := by
  by_cases h : ∃ j, b j ∉ N.closure ∅
  · obtain ⟨j,hj⟩ := h
    have hjA : b j ∈ N.closure (Set.range a) :=
      he.symm ▸ N.mem_closure_of_mem' ⟨j,rfl⟩ (hb ⟨j,rfl⟩)
    obtain ⟨i,hi⟩ := exists_generating_tuple_exchange N a (b j) ha hjA hj
    exact ⟨i,j,hi⟩
  · have hB : ∀ j, b j ∈ N.closure ∅ := by simpa only [not_exists,not_not] using h
    have hBE : N.closure (Set.range b) ⊆ N.closure ∅ := by
      apply N.closure_subset_closure_of_subset_closure
      rintro x ⟨j,rfl⟩
      exact hB j
    have hA (i) : a i ∈ N.closure ∅ :=
      hBE (he ▸ N.mem_closure_of_mem' ⟨i,rfl⟩ (ha ⟨i,rfl⟩))
    let i : Fin n := ⟨0,hn⟩
    let c := Function.update a i (b i)
    have hEmptyC : N.closure ∅ ⊆ N.closure (Set.range c) :=
      N.closure_subset_closure (Set.empty_subset _)
    have hEmptyA : N.closure ∅ ⊆ N.closure (Set.range a) :=
      N.closure_subset_closure (Set.empty_subset _)
    refine ⟨i,i,Set.Subset.antisymm ?_ ?_⟩
    · apply N.closure_subset_closure_of_subset_closure
      rintro x ⟨k,rfl⟩
      by_cases hk : k = i
      · subst k
        simpa only [Function.update_self] using hEmptyA (hB i)
      · rw [Function.update_of_ne hk]
        exact hEmptyA (hA k)
    · apply N.closure_subset_closure_of_subset_closure
      rintro x ⟨k,rfl⟩
      exact hEmptyC (hA k)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_algebraic_iff_mem_tuple_closure (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n : ℕ} (a : Fin n → RVInfinity M) (x : RVInfinity M) :
    AlgebraicAt (S ∪ Set.range (rvValues a)) .rv x.val ↔
      x ∈ (rvAlgebraicMatroid hc hex S).closure (Set.range a) := by
  rw [rvAlgebraicMatroid_closure]
  change AlgebraicAt (S ∪ Set.range (rvValues a)) .rv x.val ↔
    AlgebraicAt (S ∪ rvParameterNames (Set.range a)) .rv x.val
  rw [rvParameterNames_range]

theorem rv_tuple_closure_eq_of_interalgebraic (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {n m : ℕ}
    (a : Fin n → RVInfinity M) (b : Fin m → RVInfinity M)
    (hab : ∀ j, AlgebraicAt (S ∪ Set.range (rvValues a)) .rv (b j).val)
    (hba : ∀ i, AlgebraicAt (S ∪ Set.range (rvValues b)) .rv (a i).val) :
    (rvAlgebraicMatroid hc hex S).closure (Set.range a) =
      (rvAlgebraicMatroid hc hex S).closure (Set.range b) := by
  apply Set.Subset.antisymm <;> apply Matroid.closure_subset_closure_of_subset_closure
  · rintro x ⟨i,rfl⟩
    exact (rv_algebraic_iff_mem_tuple_closure hc hex S b (a i)).mp (hba i)
  · rintro x ⟨j,rfl⟩
    exact (rv_algebraic_iff_mem_tuple_closure hc hex S a (b j)).mp (hab j)

end DiamondIntegral.Section6
