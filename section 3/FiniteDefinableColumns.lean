import «section 3».FiniteColumnPartition
import Mathlib.Data.Set.Card
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {X Y : Type}

/-- Finite columns can be partitioned using only definable separating
rows. No column representative is named in the resulting pieces. -/
theorem finite_definable_column_partition (R : Y → X → Prop) (Def : Set X → Prop)
    (chooseCut : ∀ A, Def A →
      (∃ x ∈ A, ∃ u ∈ A, relationColumn R x ≠ relationColumn R u) →
      ∃ y, Def (A ∩ {x | R y x}) ∧ Def (A \ {x | R y x}) ∧
        (∃ x ∈ A, R y x) ∧ (∃ u ∈ A, ¬ R y u))
    (D : Set X) (hD : Def D) (hfin : (relationColumn R '' D).Finite) :
    ∃ P : Finset (Set X),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ D ∧ Def W ∧
        ∀ x ∈ W, ∀ u ∈ W, relationColumn R x = relationColumn R u) ∧
      (P : Set (Set X)).Pairwise Disjoint ∧ D = {x | ∃ W ∈ P, x ∈ W} := by
  classical
  generalize hn : (relationColumn R '' D).ncard = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hne : D.Nonempty
    · by_cases hc : ∃ x ∈ D, ∃ u ∈ D, relationColumn R x ≠ relationColumn R u
      · obtain ⟨y,hL,hU,⟨x,hx,hxy⟩,⟨u,hu,huy⟩⟩ := chooseCut D hD hc
        let L := D ∩ {x | R y x}
        let U := D \ {x | R y x}
        have hLD : L ⊆ D := fun _ h => h.1
        have hUD : U ⊆ D := fun _ h => h.1
        have hLC : relationColumn R '' L ⊆ relationColumn R '' D := Set.image_mono hLD
        have hUC : relationColumn R '' U ⊆ relationColumn R '' D := Set.image_mono hUD
        have hLU : Disjoint L U := by
          apply Set.disjoint_left.mpr
          exact fun z hz hz' => hz'.2 hz.2
        have hltL : (relationColumn R '' L).ncard < n := by
          rw [← hn]
          apply Set.ncard_lt_ncard _ hfin
          refine ⟨hLC,?_⟩
          intro hrev
          obtain ⟨z,hz,he⟩ := hrev ⟨u,hu,rfl⟩
          have hy : y ∈ relationColumn R u := he ▸ hz.2
          exact huy hy
        have hltU : (relationColumn R '' U).ncard < n := by
          rw [← hn]
          apply Set.ncard_lt_ncard _ hfin
          refine ⟨hUC,?_⟩
          intro hrev
          obtain ⟨z,hz,he⟩ := hrev ⟨x,hx,rfl⟩
          have hy : y ∈ relationColumn R z := he.symm ▸ hxy
          exact hz.2 hy
        obtain ⟨P,hP,hDisP,hCovP⟩ := ih _ hltL L hL (hfin.subset hLC) rfl
        obtain ⟨Q,hQ,hDisQ,hCovQ⟩ := ih _ hltU U hU (hfin.subset hUC) rfl
        refine ⟨P ∪ Q,?_,?_,?_⟩
        · intro W hW
          rcases Finset.mem_union.mp hW with hW | hW
          · exact ⟨(hP W hW).1,((hP W hW).2.1).trans hLD,(hP W hW).2.2⟩
          · exact ⟨(hQ W hW).1,((hQ W hW).2.1).trans hUD,(hQ W hW).2.2⟩
        · intro W hW V hV hWV
          rcases Finset.mem_union.mp hW with hW | hW <;>
            rcases Finset.mem_union.mp hV with hV | hV
          · exact hDisP hW hV hWV
          · exact hLU.mono (hP W hW).2.1 (hQ V hV).2.1
          · exact hLU.symm.mono (hQ W hW).2.1 (hP V hV).2.1
          · exact hDisQ hW hV hWV
        · ext z
          constructor
          · intro hz
            by_cases hy : R y z
            · obtain ⟨W,hW,hzW⟩ := (Set.ext_iff.mp hCovP z).mp ⟨hz,hy⟩
              exact ⟨W,Finset.mem_union_left Q hW,hzW⟩
            · obtain ⟨W,hW,hzW⟩ := (Set.ext_iff.mp hCovQ z).mp ⟨hz,hy⟩
              exact ⟨W,Finset.mem_union_right P hW,hzW⟩
          · rintro ⟨W,hW,hzW⟩
            rcases Finset.mem_union.mp hW with hW | hW
            · exact hLD ((hP W hW).2.1 hzW)
            · exact hUD ((hQ W hW).2.1 hzW)
      · refine ⟨{D},?_,?_,?_⟩
        · intro W hW
          have he : W = D := Finset.mem_singleton.mp hW
          subst W
          exact ⟨hne,Set.Subset.rfl,hD,fun x hx u hu => by by_contra hn; exact hc ⟨x,hx,u,hu,hn⟩⟩
        · simpa only [Finset.coe_singleton] using (Set.pairwise_singleton D (Disjoint : Set X → Set X → Prop))
        · ext z
          simp only [Finset.mem_singleton,exists_eq_left,Set.mem_ofPred_eq]
    · refine ⟨∅,by simp,by simp,?_⟩
      have he : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.notMem_empty,false_and,exists_false,Set.ofPred_false]
end DiamondIntegral.Section3
