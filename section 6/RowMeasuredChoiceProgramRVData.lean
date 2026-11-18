import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».ChoiceProgramRVData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».FiniteProgramChoicePartitions

/-! (Row-form version for Remark 6.20, translated from `MeasuredChoiceProgramRVData`.)
 One complete measured data relation for a finite formula-choice family.
Unit markers retain the choice even on empty fibres. Packed-row
constancy recovers the choice, every geometric datum, and the full terminal Gamma graph of its selected program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.measuredRVTrace_unit_mem_row
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (⟨1,unitRVDataTemplate S p⟩ : RVDataTemplate (M := M) S p) ∈ T.measuredRVTraceRow A P W :=
  List.mem_append.mpr (Or.inl (T.rvTrace_unit_mem A P))

def measuredChoiceProgramRVTraceRow
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) : List (RVDataTemplate (M := M) S p) :=
  (List.ofFn (fun i => restrictRVTrace ((T i).2.measuredRVTraceRow A P W) (C i) (hC i))).flatten

theorem measuredChoiceProgramRVTrace_entry_mem_row
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (i : Fin l) (D : RVDataTemplate (M := M) S p) (hD : D ∈ (T i).2.measuredRVTraceRow A P W) :
    (⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ : RVDataTemplate (M := M) S p) ∈ measuredChoiceProgramRVTraceRow T A P W C hC := by
  apply List.mem_flatten.mpr
  refine ⟨restrictRVTrace ((T i).2.measuredRVTraceRow A P W) (C i) (hC i),List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨D,hD,rfl⟩

theorem measuredChoiceProgramRVTrace_bounded_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (hForm : ∀ i,∀ a ∈ C i,∃ ω : RowFormOn (A.fibre a) qR,
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ rowFormExtension ω (x,u)=γ})
    (a : Fin p → M) : RVTraceRowsBounded a (measuredChoiceProgramRVTraceRow T A P W C hC) := by
  intro D hD
  obtain ⟨E,hE,hDE⟩ := List.mem_flatten.mp hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE
  apply restrictRVTrace_bounded ((T i).2.measuredRVTraceRow A P W) (C i) (hC i) a _ D hDE
  intro ha
  obtain ⟨ω,hW,hLevels⟩ := hForm i a ha
  exact (T i).2.measuredRVTrace_bounded_row h00 hc linear hκ hs hv hsmall hΓ A P W a
    (hValid i a ha).1 (hValid i a ha).2 ω hW hLevels

def measuredChoiceProgramRVDataRow
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :=
  packedRVTrace (measuredChoiceProgramRVTraceRow T A P W C hC)

theorem measuredChoiceProgramRVData_doublyBounded_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (hValid : ∀ i,∀ a ∈ C i,a ∈ (T i).2.good A P ∧ TemplateFibreGeometry A P a)
    (hForm : ∀ i,∀ a ∈ C i,∃ ω : RowFormOn (A.fibre a) qR,
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ rowFormExtension ω (x,u)=γ})
    (a : Fin p → M) : RVValueDoublyBounded ((measuredChoiceProgramRVDataRow T A P W C hC).fibre a).carrier :=
  packedRVTrace_doublyBounded _ a (measuredChoiceProgramRVTrace_bounded_row h00 hc hκ hs hv linear hsmall hΓ T A P W C hC hValid hForm a)

theorem choices_eq_of_measured_program_data_eq_row
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVDataRow T A P W C hC).fibre a).carrier=((measuredChoiceProgramRVDataRow T A P W C hC).fibre b).carrier) :
    ∀ i,a ∈ C i ↔ b ∈ C i := by
  intro i
  have hRows := trace_rows_eq_of_packed_eq h00 (measuredChoiceProgramRVTraceRow T A P W C hC) a b he
    ⟨1,(unitRVDataTemplate S p).restrictParameters (C i) (hC i)⟩
    (measuredChoiceProgramRVTrace_entry_mem_row T A P W C hC i _ ((T i).2.measuredRVTrace_unit_mem_row A P W))
  rw [← restricted_unit_nonempty_iff (C i) (hC i) a,← restricted_unit_nonempty_iff (C i) (hC i) b,hRows]

theorem selected_trace_rows_eq_of_measured_program_data_eq_row
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVDataRow T A P W C hC).fibre a).carrier=((measuredChoiceProgramRVDataRow T A P W C hC).fibre b).carrier)
    (i : Fin l) (ha : a ∈ C i) :
    ∀ D ∈ (T i).2.measuredRVTraceRow A P W,(D.2.fibre a).carrier=(D.2.fibre b).carrier := by
  intro D hD
  have hb := (choices_eq_of_measured_program_data_eq_row h00 T A P W C hC a b he i).mp ha
  have hRows := trace_rows_eq_of_packed_eq h00 (measuredChoiceProgramRVTraceRow T A P W C hC) a b he
    ⟨D.1,D.2.restrictParameters (C i) (hC i)⟩ (measuredChoiceProgramRVTrace_entry_mem_row T A P W C hC i D hD)
  rw [RVSetParameterTemplate.restrictParameters_fibre,RVSetParameterTemplate.restrictParameters_fibre] at hRows
  ext u
  have hAt := Set.ext_iff.mp hRows u
  simpa only [Set.mem_setOf_eq,ha,hb,true_and] using hAt

end DiamondIntegral.Section6
