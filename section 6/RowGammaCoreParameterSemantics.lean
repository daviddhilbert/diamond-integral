import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».GammaCoreParameterSemantics

/-! (Row-form version for Remark 6.20, replacing `GammaCoreParameterSemantics`.)
The core-row parameter test has exact semantics on actual transition
graphs: equal rows for true-branch points whose targets agree off the active
coordinate and on all output labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s qR : ℕ}

theorem gammaCoreJointGraph_entries_row
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (coreTag : Fin s) (x : GammaTransitionEntryRow n r s qR → M) :
    Sum.elim a x ∈ gammaCoreJointGraphRow R W coreTag ↔
      ∃ t : A, ∃ c : (rawRVSpace (M := M) qR).domain,
        ((rawRVSpace (M := M) qR).decode c ∈ (ω t).val ∨
          (rawRVSpace (M := M) qR).decode c = RowFormOn.rowMarker M qR) ∧
        x = Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val) ∧
        (f t).val.2 coreTag = branchTag true := by
  constructor
  · rintro ⟨hx, hFlag⟩
    obtain ⟨t, c, hc, rfl⟩ := (gammaTransitionJointGraph_entries_row a R W f ω hR hW x).mp hx
    exact ⟨t, c, hc, rfl, Subtype.ext hFlag⟩
  · rintro ⟨t, c, hc, rfl, hFlag⟩
    refine ⟨(gammaTransitionJointGraph_entries_row a R W f ω hR hW _).mpr ⟨t, c, hc, rfl⟩, ?_⟩
    exact congrArg Subtype.val hFlag

theorem gammaCoreConstantParameterLocus_iff_row [NeZero qR]
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (j : Fin n) (coreTag : Fin s) :
    a ∈ gammaCoreConstantParameterLocusRow R W j coreTag ↔
      ∀ t u : A, (f t).val.2 coreTag = branchTag true → (f u).val.2 coreTag = branchTag true →
        (f t).val.2 = (f u).val.2 →
          (∀ i, i ≠ j → (f t).val.1 i = (f u).val.1 i) → (ω t).val = (ω u).val := by
  constructor
  · intro h t u ht hu hTags hOther
    have hVF : ∀ i, i ≠ j → (mixedValues (f t).val) (.inl i) = (mixedValues (f u).val) (.inl i) := by
      intro i hi
      exact congrArg Subtype.val (hOther i hi)
    have hRV : ∀ i : Fin s, (mixedValues (f t).val) (.inr i) = (mixedValues (f u).val) (.inr i) := by
      intro i
      exact congrArg (fun v => (v i).val) hTags
    have hTransfer (t u : A) (ht : (f t).val.2 coreTag = branchTag true)
        (hu : (f u).val.2 coreTag = branchTag true)
        (hVF : ∀ i, i ≠ j → (mixedValues (f t).val) (.inl i) = (mixedValues (f u).val) (.inl i))
        (hRV : ∀ i : Fin s, (mixedValues (f t).val) (.inr i) = (mixedValues (f u).val) (.inr i))
        (v : (rawRVSpace (M := M) qR).Carrier) (hv : v ∈ (ω t).val) : v ∈ (ω u).val := by
      have hx := (gammaCoreJointGraph_entries_row a R W f ω hR hW coreTag _).mpr
        ⟨t, rowCode v, Or.inl ((decode_rowCode v).symm ▸ hv), rfl, ht⟩
      have hy := (gammaCoreJointGraph_entries_row a R W f ω hR hW coreTag _).mpr
        ⟨u, rowMarkerCode M qR, Or.inr (decode_rowMarkerCode qR), rfl, hu⟩
      have hC := h _ _ hx hy hVF hRV
      rcases (rowGraph_entry_iff a W ω hW u (rowCode v)).mp hC with h2 | h2
      · exact decode_rowCode v ▸ h2
      · rw [decode_rowCode] at h2
        exact absurd (h2 ▸ hv) (RowFormOn.rowMarker_not_mem ω t)
    ext v
    exact ⟨hTransfer t u ht hu hVF hRV v,
      hTransfer u t hu ht (fun i hi => (hVF i hi).symm) (fun i => (hRV i).symm) v⟩
  · intro h x y hx hy
    obtain ⟨t, c, hc, rfl, ht⟩ := (gammaCoreJointGraph_entries_row a R W f ω hR hW coreTag x).mp hx
    obtain ⟨u, d, hd, rfl, hu⟩ := (gammaCoreJointGraph_entries_row a R W f ω hR hW coreTag y).mp hy
    intro hOther hTags
    have hRV : (f t).val.2 = (f u).val.2 := funext (fun i => Subtype.ext (hTags i))
    have hVF : ∀ i, i ≠ j → (f t).val.1 i = (f u).val.1 i :=
      fun i hi => Subtype.ext (hOther i hi)
    apply (rowGraph_entry_iff a W ω hW u c).mpr
    rw [← h t u ht hu hRV hVF]
    exact hc

end DiamondIntegral.Section6
