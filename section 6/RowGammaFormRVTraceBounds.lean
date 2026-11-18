import «section 6».RowGammaFormRVTraces
import «section 6».GammaFormRVTraceBounds

/-! (Row-form version for Remark 6.20, replacing `GammaFormRVTraceBounds`.)
Row RV traces have doubly bounded rows: labels are bounded by the proper
source and row entries by the intrinsic bound of the row form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r qR : ℕ} [NeZero qR]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaForm_value_bounds_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : ProperInvariant S A.carrier)
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∃ β : Gamma M, ∀ t : A, ∀ v ∈ (ω t).val, ∀ i,
      (β⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ β.val :=
  ω.bounded

theorem GammaFormParameterTemplateRow.rvTrace_doublyBounded_of_bounds_row
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : RowFormOn A qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hRV : RVSupportDoublyBounded A.carrier)
    (hBounds : ∃ δ : Gamma M, ∀ t : A, ∀ v ∈ (ω t).val, ∀ i,
      (δ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ δ.val) :
    RVValueDoublyBounded (W.rvTrace.fibre a).carrier := by
  obtain ⟨β,hβ⟩ := hRV
  obtain ⟨δ,hδ⟩ := hBounds
  let ρ := max β δ
  have hβρ : β ≤ ρ := le_max_left _ _
  have hδρ : δ ≤ ρ := le_max_right _ _
  refine ⟨ρ,?_⟩
  intro v hv i
  obtain ⟨t,hTags,hRow⟩ := (W.rvTrace_entries_row a ω hW v).mp hv
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h := hβ t.val t.property j
    rw [hTags] at h
    exact ⟨(show (ρ⁻¹).val ≤ (β⁻¹).val from inv_le_inv' hβρ).trans h.1,
      h.2.trans (show β.val ≤ ρ.val from hβρ)⟩
  · have h := hδ t _ hRow j
    exact ⟨(show (ρ⁻¹).val ≤ (δ⁻¹).val from inv_le_inv' hδρ).trans h.1,
      h.2.trans (show δ.val ≤ ρ.val from hδρ)⟩

theorem GammaFormParameterTemplateRow.rvTrace_doublyBounded_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (hA : ProperInvariant (S ∪ Set.range a) A.carrier)
    (ω : RowFormOn A qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    RVValueDoublyBounded (W.rvTrace.fibre a).carrier :=
  W.rvTrace_doublyBounded_of_bounds_row a ω hW hA.rvBounded ω.bounded

end DiamondIntegral.Section6
