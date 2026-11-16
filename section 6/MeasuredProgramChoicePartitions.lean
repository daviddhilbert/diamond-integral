import «section 6».FormCompatibleProgramLoci

/-! The finite formula-choice cover for complete programs has a
same-base definable disjoint refinement. These are the choice pieces
included in the complete data before unary freezing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k l : ℕ}

theorem exists_disjoint_measured_program_choice
    (X : Set (Fin p → M)) (hX : S.Definable LRV X)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (hCover : ∀ a ∈ X,∃ i,a ∈ (T i).2.measuredFormGood A P W) :
    ∃ C : Fin l → Set (Fin p → M),(∀ i,S.Definable LRV (C i)) ∧
      (∀ i,C i ⊆ X ∩ (T i).2.measuredFormGood A P W) ∧
      (∀ a ∈ X,∃ i,a ∈ C i) ∧ (∀ i j a,a ∈ C i → a ∈ C j → i=j) := by
  let earlier (i : Fin l) : Set (Fin p → M) :=
    ⋃ j : {j : Fin l // j < i},(T j.val).2.measuredFormGood A P W
  let C (i : Fin l) := (X ∩ (T i).2.measuredFormGood A P W) \ earlier i
  have hEarlier (i) : S.Definable LRV (earlier i) :=
    Set.definable_iUnion_of_finite (fun j => (T j.val).2.measuredFormGood_definable A P W)
  have memEarlier (i : Fin l) (a : Fin p → M) : a ∈ earlier i ↔
      ∃ j,j < i ∧ a ∈ (T j).2.measuredFormGood A P W := by
    simp only [earlier,Set.mem_iUnion,Subtype.exists,exists_prop]
  refine ⟨C,(fun i => (hX.inter ((T i).2.measuredFormGood_definable A P W)).sdiff (hEarlier i)),
    (fun _ => Set.sdiff_subset),?_,?_⟩
  · intro a ha
    let I := Finset.univ.filter (fun i => a ∈ (T i).2.measuredFormGood A P W)
    have hI : I.Nonempty := by
      obtain ⟨i,hi⟩ := hCover a ha
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    let i := I.min' hI
    refine ⟨i,⟨ha,(Finset.mem_filter.mp (I.min'_mem hI)).2⟩,?_⟩
    intro h
    obtain ⟨j,hji,hj⟩ := (memEarlier i a).mp h
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    exact (not_lt_of_ge (I.min'_le j hjI)) hji
  · intro i j a hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (hj.2 ((memEarlier j a).mpr ⟨i,h,hi.1.2⟩)).elim
    · exact h
    · exact (hi.2 ((memEarlier i a).mpr ⟨j,h,hj.1.2⟩)).elim

end DiamondIntegral.Section6
