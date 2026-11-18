import «section 6».RowGammaTransitionImages
import «section 6».GammaFormRVTraces

/-! (Row-form version for Remark 6.20, replacing `GammaFormRVTraces`.)
A row template has an original-base RV trace: the old labels followed by the
row entries. Its rows are exactly the membership records of the actual row
form; no code is involved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r qR : ℕ} [NeZero qR]

def gammaFormRVTraceGraphRow
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : Set (Fin p ⊕ Fin (r+qR) → M) :=
  {z | (∃ x : Fin n → M, Sum.elim (z ∘ Sum.inl)
    (Sum.elim (Sum.elim x (fun j => z (.inr (Fin.castAdd qR j))))
      (fun j : Fin qR => z (.inr (Fin.natAdd r j)))) ∈ W.graph) ∧
    ¬ ∀ j : Fin qR, z (.inr (Fin.natAdd r j)) = iRVZero}

theorem gammaFormRVTraceGraph_definable_row
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    S.Definable LRV (gammaFormRVTraceGraphRow W) := by
  let Z := (Fin p ⊕ Fin (r+qR)) ⊕ Fin n
  have hCode : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (Sum.elim (z ∘ Sum.inr) (fun j => z (.inl (.inr (Fin.castAdd qR j)))))
        (fun j : Fin qR => z (.inl (.inr (Fin.natAdd r j)))))) := by
    rintro (i | ((i | i) | i)) <;> exact Set.DefinableFun.proj LRV
  have hMark (j : Fin qR) : S.Definable LRV {z : Fin p ⊕ Fin (r+qR) → M | z (.inr (Fin.natAdd r j)) = iRVZero} :=
    SpecialTransformations.Section4.rvZero_coordinate_definable S _
  convert (W.definable.preimage_map hCode).exists_of_finite.inter (Set.definable_iInter_of_finite hMark).compl using 1
  ext z
  simp only [gammaFormRVTraceGraphRow, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter]
  rfl

def GammaFormParameterTemplateRow.rvTrace (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    RVSetParameterTemplate (M := M) S p (r+qR) :=
  ⟨gammaFormRVTraceGraphRow W, gammaFormRVTraceGraph_definable_row W⟩

theorem rowMarker_eq_iff (v : Fin qR → RVInfinity M) :
    v = RowFormOn.rowMarker M qR ↔ ∀ j, (v j).val = iRVZero := by
  constructor
  · rintro rfl j
    exact RVOperations.zero_val
  · intro h
    funext j
    exact Subtype.ext ((h j).trans RVOperations.zero_val.symm)

theorem GammaFormParameterTemplateRow.rvTrace_entries_row [NeZero qR]
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : RowFormOn A qR)
    (hW : {z | Sum.elim a z ∈ W.graph} = (rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (v : Fin (r+qR) → RVInfinity M) :
    v ∈ (W.rvTrace.fibre a).carrier ↔
      ∃ t : A, t.val.2 = (fun j => v (Fin.castAdd qR j)) ∧ (fun j => v (Fin.natAdd r j)) ∈ (ω t).val := by
  change (∃ x : Fin n → M, Sum.elim a
    (Sum.elim (Sum.elim x (fun j => (v (Fin.castAdd qR j)).val))
      (fun j : Fin qR => (v (Fin.natAdd r j)).val)) ∈ W.graph) ∧
      ¬ (∀ j : Fin qR, (v (Fin.natAdd r j)).val = iRVZero) ↔ _
  constructor
  · rintro ⟨⟨x, hx⟩, hNot⟩
    obtain ⟨hDom, hc, t, ht, hVal⟩ := (Set.ext_iff.mp hW _).mp hx
    have hInput : mixedValues t.val = Sum.elim x (fun j => (v (Fin.castAdd qR j)).val) := by
      rw [ht]
      exact mixedValues_decode _
    have hdec : (rawRVSpace (M := M) qR).decode ⟨_, hc⟩ = (fun j => v (Fin.natAdd r j)) :=
      rvValues_injective (rvValues_decode (M := M) ⟨_, hc⟩)
    rw [hdec] at hVal
    refine ⟨t, funext (fun j => Subtype.ext (congrFun hInput (.inr j))), ?_⟩
    rcases hVal with hVal | hVal
    · exact hVal
    · exact absurd ((rowMarker_eq_iff _).mp hVal) hNot
  · rintro ⟨t, hTags, hVal⟩
    refine ⟨⟨vfValues t.val.1, ?_⟩, fun hAll => RowFormOn.rowMarker_not_mem ω t
      (((rowMarker_eq_iff _).mpr hAll) ▸ hVal)⟩
    apply (Set.ext_iff.mp hW _).mpr
    have hInput : Sum.elim (vfValues t.val.1) (fun j => (v (Fin.castAdd qR j)).val) = mixedValues t.val := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (congrArg (fun u => (u i).val) hTags).symm
    have hDom : Sum.elim (vfValues t.val.1) (fun j => (v (Fin.castAdd qR j)).val) ∈
        (rawMixedSpace (M := M) n r).domain := hInput.symm ▸ mixedValues_mem_domain t.val
    have hc : (fun j : Fin qR => (v (Fin.natAdd r j)).val) ∈ (rawRVSpace (M := M) qR).domain :=
      ⟨fun j => v (Fin.natAdd r j), rfl⟩
    have hdec : (rawRVSpace (M := M) qR).decode ⟨_, hc⟩ = (fun j => v (Fin.natAdd r j)) :=
      rvValues_injective (rvValues_decode (M := M) ⟨_, hc⟩)
    refine ⟨hDom, hc, t, ?_, Or.inl (hdec.symm ▸ hVal)⟩
    exact (mixedValues_injective ((mixedValues_decode _).trans hInput)).symm

end DiamondIntegral.Section6
