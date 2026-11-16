import «section 6».FiniteBranchedShearTemplates

/-! A finite definable cover has an original-base definable disjoint
choice partition, selecting the first valid member of the cover. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] {S : Set M} {p k : ℕ}

theorem exists_disjoint_definable_finite_choice
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (Q : Fin k → Set (Fin p → M)) (hQ : ∀ i,S.Definable LRV (Q i))
    (hCover : ∀ a ∈ U,∃ i,a ∈ Q i) :
    ∃ C : Fin k → Set (Fin p → M),(∀ i,S.Definable LRV (C i)) ∧
      (∀ i,C i ⊆ U ∩ Q i) ∧ (∀ a ∈ U,∃ i,a ∈ C i) ∧
      (∀ i j a,a ∈ C i → a ∈ C j → i=j) := by
  let earlier (i : Fin k) : Set (Fin p → M) := ⋃ j : {j : Fin k // j < i},Q j.val
  let C (i : Fin k) := (U ∩ Q i) \ earlier i
  have hEarlier (i) : S.Definable LRV (earlier i) := Set.definable_iUnion_of_finite (fun j => hQ j.val)
  have memEarlier (i : Fin k) (a : Fin p → M) : a ∈ earlier i ↔ ∃ j,j < i ∧ a ∈ Q j := by
    simp only [earlier,Set.mem_iUnion,Subtype.exists,exists_prop]
  refine ⟨C,(fun i => (hU.inter (hQ i)).sdiff (hEarlier i)),(fun _ => Set.sdiff_subset),?_,?_⟩
  · intro a ha
    let I := Finset.univ.filter (fun i => a ∈ Q i)
    have hI : I.Nonempty := by
      obtain ⟨i,hi⟩ := hCover a ha
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    let i := I.min' hI
    refine ⟨i,⟨ha,(Finset.mem_filter.mp (I.min'_mem hI)).2⟩,?_⟩
    intro h
    obtain ⟨j,hji,hj⟩ := (memEarlier i a).mp h
    exact (not_lt_of_ge (I.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))) hji
  · intro i j a hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (hj.2 ((memEarlier j a).mpr ⟨i,h,hi.1.2⟩)).elim
    · exact h
    · exact (hi.2 ((memEarlier i a).mpr ⟨j,h,hj.1.2⟩)).elim

end DiamondIntegral.Section6
