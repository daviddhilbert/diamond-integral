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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
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
import «section 6».SequentialCentripetalPrograms
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowFormCompatibleProgramLoci

/-! (Row-form version for Remark 6.20, translated from `SequentialMeasuredCentripetalPrograms`.)
 Sequential normalization retains each component form guard, the
full terminal Gamma graph and all measured admissibility tests. Gamma
graph transportRow composes by actual first-order existential projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t v k : ℕ}

theorem gammaTransitionImage_comp_row
    (F : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (H : Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (Fin n ⊕ Fin t)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) :
    gammaTransitionImageRow (parameterRelationComp F H) W=gammaTransitionImageRow H (gammaTransitionImageRow F W) := by
  ext z
  constructor
  · rintro ⟨x,⟨y,hF,hH⟩,hW⟩
    exact ⟨y,hH,x,hF,hW⟩
  · rintro ⟨y,hH,x,hF,hW⟩
    exact ⟨x,⟨y,hF,hH⟩,hW⟩

theorem GammaFormParameterTemplateRow.transport_program_comp_row
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    W.transportRow ((F.comp H).transition A)=(W.transportRow (F.transition A)).transportRow (H.transition (F.target A)) := by
  apply GammaFormParameterTemplateRow.ext_graph
  exact gammaTransitionImage_comp_row _ _ _

structure CentripetalProgramTemplate.SameFormDataRow
    (F H : CentripetalProgramTemplate (M := M) S p n r s) : Prop extends F.SameData H where
  coreFormGoodRow : ∀ {q : ℕ} [NeZero q] (A : MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplateRow (qR := q) (M := M) S p n r),F.coreFormGoodRow A W=H.coreFormGoodRow A W

namespace CentripetalProgramTemplate.SameFormDataRow

theorem refl (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameFormDataRow F :=
  ⟨.refl F,fun _ _ => rfl⟩

theorem trans {F H K : CentripetalProgramTemplate (M := M) S p n r s}
    (hFH : F.SameFormDataRow H) (hHK : H.SameFormDataRow K) : F.SameFormDataRow K :=
  ⟨hFH.toSameData.trans hHK.toSameData,fun A W => (hFH.coreFormGoodRow A W).trans (hHK.coreFormGoodRow A W)⟩

theorem comp {F F' : CentripetalProgramTemplate (M := M) S p n r s}
    {H H' : CentripetalProgramTemplate (M := M) S p n s t}
    (hF : F.SameFormDataRow F') (hH : H.SameFormDataRow H') : (F.comp H).SameFormDataRow (F'.comp H') := by
  refine ⟨hF.toSameData.comp hH.toSameData,?_⟩
  intro _ _ A W
  change F.coreFormGoodRow A W ∩ H.coreFormGoodRow (F.target A) (W.transportRow (F.transition A))=_
  rw [hF.coreFormGoodRow,hF.toSameData.target,hF.toSameData.transition,hH.coreFormGoodRow]
  rfl

theorem assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (K : CentripetalProgramTemplate (M := M) S p n t v) :
    ((F.comp H).comp K).SameFormDataRow (F.comp (H.comp K)) := by
  refine ⟨.assoc F H K,?_⟩
  intro _ _ A W
  change (F.coreFormGoodRow A W ∩ H.coreFormGoodRow (F.target A) (W.transportRow (F.transition A))) ∩
      K.coreFormGoodRow ((F.comp H).target A) (W.transportRow ((F.comp H).transition A))=_
  rw [F.target_comp H A,W.transport_program_comp_row F H A]
  exact Set.inter_assoc _ _ _

theorem measuredGoodRow {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormDataRow H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : F.measuredGoodRow A P W=H.measuredGoodRow A P W := by
  unfold CentripetalProgramTemplate.measuredGoodRow
  rw [h.toSameData.preparedGood A P,h.toSameData.transition A]

theorem measuredFormGoodRow {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormDataRow H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : F.measuredFormGoodRow A P W=H.measuredFormGoodRow A P W := by
  unfold CentripetalProgramTemplate.measuredFormGoodRow
  rw [h.measuredGoodRow A P W,h.coreFormGoodRow A W]

theorem measuredRVTraceRow {F H : CentripetalProgramTemplate (M := M) S p n r s}
    (h : F.SameFormDataRow H) (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : F.measuredRVTraceRow A P W=H.measuredRVTraceRow A P W := by
  unfold CentripetalProgramTemplate.measuredRVTraceRow CentripetalProgramTemplate.gammaRVTraceRow
  rw [h.toSameData.rvTrace A P,h.toSameData.transition A]

end CentripetalProgramTemplate.SameFormDataRow

theorem CentripetalProgramSequence.append_sameFormData_row
    (F : CentripetalProgramSequence (M := M) S p n r s)
    (H : CentripetalProgramSequence (M := M) S p n s t) :
    (F.toProgram.comp H.toProgram).SameFormDataRow (F.append H).toProgram := by
  induction F with
  | single F => exact CentripetalProgramTemplate.SameFormDataRow.refl _
  | cons F K ih =>
    exact (CentripetalProgramTemplate.SameFormDataRow.assoc F.toProgram K.toProgram H.toProgram).trans
      ((CentripetalProgramTemplate.SameFormDataRow.refl F.toProgram).comp (ih H))

theorem CentripetalProgramTemplate.toSequence_sameFormData_row
    (F : CentripetalProgramTemplate (M := M) S p n r s) : F.SameFormDataRow F.toSequence.toProgram := by
  induction F with
  | identity r => exact CentripetalProgramTemplate.SameFormDataRow.refl _
  | regularize r => exact CentripetalProgramTemplate.SameFormDataRow.refl _
  | centripetal T => exact CentripetalProgramTemplate.SameFormDataRow.refl _
  | comp F H ihF ihH => exact (ihF.comp ihH).trans (F.toSequence.append_sameFormData_row H.toSequence)

end DiamondIntegral.Section6
