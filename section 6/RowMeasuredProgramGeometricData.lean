import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFiniteFormCompatiblePrograms
import «section 6».RowFiniteHeadFormCompatiblePrograms
import «section 6».RowFiniteHeadMeasuredPrograms
import «section 6».RowFiniteMeasuredCentripetalPrograms
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormFreezing
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowHeadGammaFormMaps
import «section 6».RowHeadGammaFormTemplates
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredChoiceProgramRVData
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramChoicePartitions
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedFormCompatiblePrograms
import «section 6».RowPromotedFormCompatiblePrograms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
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
import «section 6».RowMeasuredCoordinateProgramData

/-! (Row-form version for Remark 6.20, translated from `MeasuredProgramGeometricData`.)
 The complete measured record recovers the exact older geometric
record. This lets the existing actual fusion constructions be reused
while the additional full Gamma graph remains available. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k l : ℕ}

theorem packedRVTrace_eq_of_rows_eq_row
    (D : List (RVDataTemplate (M := M) S p)) (a b : Fin p → M)
    (he : ∀ T ∈ D,(T.2.fibre a).carrier=(T.2.fibre b).carrier) :
    ((packedRVTrace D).fibre a).carrier=((packedRVTrace D).fibre b).carrier := by
  unfold packedRVTrace packedRVDataFamily
  rw [RVSetParameterTemplate.finiteUnion_fibre,RVSetParameterTemplate.finiteUnion_fibre]
  congr 1
  funext i
  rw [packedRVDataTemplate_fibre,packedRVDataTemplate_fibre,he (D.get i) (List.get_mem D i)]

theorem choiceProgramRVTrace_subset_measured_row
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i)) :
    ∀ D ∈ choiceProgramRVTrace T A P C hC,D ∈ measuredChoiceProgramRVTraceRow T A P W C hC := by
  intro D hD
  obtain ⟨E,hE,hDE⟩ := List.mem_flatten.mp hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE
  obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hDE
  exact measuredChoiceProgramRVTrace_entry_mem_row T A P W C hC i F (List.mem_append.mpr (Or.inl hF))

theorem geometric_data_eq_of_measured_data_eq_row
    (h00 : M ⊨ Axioms.ACVF00)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (C : Fin l → Set (Fin p → M)) (hC : ∀ i,S.Definable LRV (C i))
    (a b : Fin p → M)
    (he : ((measuredChoiceProgramRVDataRow T A P W C hC).fibre a).carrier=
      ((measuredChoiceProgramRVDataRow T A P W C hC).fibre b).carrier) :
    ((choiceProgramRVData T A P C hC).fibre a).carrier=((choiceProgramRVData T A P C hC).fibre b).carrier := by
  apply packedRVTrace_eq_of_rows_eq_row
  intro D hD
  exact trace_rows_eq_of_packed_eq h00 _ a b he D (choiceProgramRVTrace_subset_measured_row T A P W C hC D hD)

def FiniteMeasuredCoordinateProgramDataRow.forget
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : RowFormOn A qR}
    (F : FiniteMeasuredCoordinateProgramDataRow A P ω) : FiniteCoordinateProgramData A P := {
  count := F.count
  programs := F.programs
  choices := F.choices
  choices_definable := F.choices_definable
  choices_subset := fun i a ha => ⟨(F.choices_subset i ha).1,(F.choices_subset i ha).2.1.1⟩
  cover := F.cover
  disjoint := F.disjoint
  geometry := F.geometry }

end DiamondIntegral.Section6
