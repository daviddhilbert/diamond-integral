import «section 6».RowGammaTransitionParameterLoci
import «section 6».GammaTransitionSemantics

/-! (Row-form version for Remark 6.20, replacing `GammaTransitionSemantics`.)
The first-order row test means precisely constancy of the transported row
form on equal output RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s qR : ℕ}

/-- The domain element encoding the row marker. -/
def rowMarkerCode (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (q : ℕ) :
    (rawRVSpace (M := M) q).domain :=
  ⟨rvValues (RowFormOn.rowMarker M q), ⟨_, rfl⟩⟩

theorem decode_rowMarkerCode (q : ℕ) :
    (rawRVSpace (M := M) q).decode (rowMarkerCode M q) = RowFormOn.rowMarker M q :=
  decode_rvValues _

/-- The domain element encoding a row tuple. -/
def rowCode (v : (rawRVSpace (M := M) qR).Carrier) : (rawRVSpace (M := M) qR).domain :=
  ⟨rvValues v, ⟨v, rfl⟩⟩

theorem decode_rowCode (v : (rawRVSpace (M := M) qR).Carrier) :
    (rawRVSpace (M := M) qR).decode (rowCode v) = v :=
  decode_rvValues v


theorem rowGraph_entry_iff
    (a : Fin p → M)
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : RowFormOn A qR)
    (hW : {z | Sum.elim a z ∈ W} = (rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (t : A) (c : (rawRVSpace (M := M) qR).domain) :
    Sum.elim a (Sum.elim (mixedValues t.val) c.val) ∈ W ↔
      ((rawRVSpace (M := M) qR).decode c ∈ (ω t).val ∨
        (rawRVSpace (M := M) qR).decode c = RowFormOn.rowMarker M qR) := by
  have h := Set.ext_iff.mp hW (Sum.elim (mixedValues t.val) c.val)
  change Sum.elim a (Sum.elim (mixedValues t.val) c.val) ∈ W ↔ _ at h
  rw [h, (rawMixedSpace (M := M) n r).relation_decode (rawRVSpace (M := M) qR) ω.graph
    ⟨mixedValues t.val, mixedValues_mem_domain _⟩ c, decode_mixedValues]
  constructor
  · rintro ⟨t', ht', hu⟩
    have he : t' = t := Subtype.ext ht'
    subst he
    exact hu
  · intro hu
    exact ⟨t, rfl, hu⟩

/-- Membership of the first source in the relation `W` at an arbitrary point. -/
theorem rowGraph_point_iff
    (a : Fin p → M)
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : RowFormOn A qR)
    (hW : {z | Sum.elim a z ∈ W} = (rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (x : (Fin n ⊕ Fin r) ⊕ Fin qR → M) :
    Sum.elim a x ∈ W ↔ ∃ t : A, ∃ c : (rawRVSpace (M := M) qR).domain,
      ((rawRVSpace (M := M) qR).decode c ∈ (ω t).val ∨
        (rawRVSpace (M := M) qR).decode c = RowFormOn.rowMarker M qR) ∧
      x = Sum.elim (mixedValues t.val) c.val := by
  constructor
  · intro hx
    have hrel := (Set.ext_iff.mp hW x).mp hx
    obtain ⟨hx1, hx2, t, ht, hu⟩ := hrel
    let c : (rawRVSpace (M := M) qR).domain := ⟨x ∘ Sum.inr, hx2⟩
    refine ⟨t, c, hu, ?_⟩
    · have hInput : mixedValues t.val = x ∘ Sum.inl := by
        rw [ht]
        exact mixedValues_decode _
      funext i
      rcases i with i | i
      · exact (congrFun hInput i).symm
      · rfl
  · rintro ⟨t, c, hc, rfl⟩
    exact (rowGraph_entry_iff a W ω hW t c).mpr hc

theorem gammaTransitionJointGraph_entries_row
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (x : GammaTransitionEntryRow n r s qR → M) :
    Sum.elim a x ∈ gammaTransitionJointGraphRow R W ↔
      ∃ t : A, ∃ c : (rawRVSpace (M := M) qR).domain,
        ((rawRVSpace (M := M) qR).decode c ∈ (ω t).val ∨
          (rawRVSpace (M := M) qR).decode c = RowFormOn.rowMarker M qR) ∧
        x = Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val) := by
  constructor
  · rintro ⟨hRx, hWx⟩
    obtain ⟨hx, hy, t, ht, hft⟩ := (Set.ext_iff.mp hR _).mp hRx
    have hInput : mixedValues t.val = x ∘ Sum.inl := by
      rw [ht]
      exact mixedValues_decode _
    have hOutput : mixedValues (f t).val = (fun i => x (.inr (.inl i))) := by
      rw [hft]
      exact mixedValues_decode _
    obtain ⟨t', c, hc, hxc⟩ := (rowGraph_point_iff a W ω hW _).mp hWx
    have hval : mixedValues t'.val = mixedValues t.val := by
      rw [hInput]
      funext i
      exact (congrFun hxc (.inl i)).symm
    have he : t' = t := Subtype.ext (mixedValues_injective hval)
    subst he
    refine ⟨t', c, hc, ?_⟩
    funext i
    rcases i with i | (i | i)
    · exact (congrFun hInput i).symm
    · exact (congrFun hOutput i).symm
    · exact congrFun hxc (.inr i)
  · rintro ⟨t, c, hc, rfl⟩
    constructor
    · apply (Set.ext_iff.mp hR _).mpr
      apply ((rawMixedSpace (M := M) n r).relation_decode (rawMixedSpace n s) f.graph
        ⟨mixedValues t.val, mixedValues_mem_domain _⟩ ⟨mixedValues (f t).val, mixedValues_mem_domain _⟩).mpr
      simpa only [decode_mixedValues] using (show f.graph t.val (f t).val from ⟨t, rfl, rfl⟩)
    · exact (rowGraph_entry_iff a W ω hW t c).mpr hc

theorem gammaTransitionConstantParameterLocus_iff_row [NeZero qR]
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)}
    (f : Map A B) (ω : RowFormOn A qR)
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) :
    a ∈ gammaTransitionConstantParameterLocusRow R W ↔
      ∀ t u : A, (f t).val.2 = (f u).val.2 → (ω t).val = (ω u).val := by
  have hEntry (t : A) (c : (rawRVSpace (M := M) qR).domain)
      (hc : (rawRVSpace (M := M) qR).decode c ∈ (ω t).val ∨
        (rawRVSpace (M := M) qR).decode c = RowFormOn.rowMarker M qR) :
      Sum.elim a (Sum.elim (mixedValues t.val) (Sum.elim (mixedValues (f t).val) c.val)) ∈
        gammaTransitionJointGraphRow R W :=
    (gammaTransitionJointGraph_entries_row a R W f ω hR hW _).mpr ⟨t, c, hc, rfl⟩
  constructor
  · intro h t u htu
    have hTags : ∀ j : Fin s, (mixedValues (f t).val) (.inr j) = (mixedValues (f u).val) (.inr j) := by
      intro j
      exact congrArg (fun v => (v j).val) htu
    have hTransfer (t u : A) (htu : ∀ j : Fin s, (mixedValues (f t).val) (.inr j) = (mixedValues (f u).val) (.inr j))
        (v : (rawRVSpace (M := M) qR).Carrier) (hv : v ∈ (ω t).val) : v ∈ (ω u).val := by
      have hC := h _ _ (hEntry t (rowCode v) (Or.inl ((decode_rowCode v).symm ▸ hv)))
        (hEntry u (rowMarkerCode M qR) (Or.inr (decode_rowMarkerCode qR))) htu
      rcases (rowGraph_entry_iff a W ω hW u (rowCode v)).mp hC with h2 | h2
      · exact decode_rowCode v ▸ h2
      · rw [decode_rowCode] at h2
        exact absurd (h2 ▸ hv) (RowFormOn.rowMarker_not_mem ω t)
    ext v
    exact ⟨hTransfer t u hTags v, hTransfer u t (fun j => (hTags j).symm) v⟩
  · intro h x y hx hy hTags
    obtain ⟨t, c, hc, rfl⟩ := (gammaTransitionJointGraph_entries_row a R W f ω hR hW x).mp hx
    obtain ⟨u, d, hd, rfl⟩ := (gammaTransitionJointGraph_entries_row a R W f ω hR hW y).mp hy
    have htu : (f t).val.2 = (f u).val.2 := by
      funext j
      exact Subtype.ext (hTags j)
    apply (rowGraph_entry_iff a W ω hW u c).mpr
    rw [← h t u htu]
    exact hc

end DiamondIntegral.Section6
