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
import «section 6».RowFormCompatibleProgramLoci
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
import «section 6».RowMeasuredProgramRVTraces
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
import «section 6».RowSequentialMeasuredCentripetalPrograms
import «section 6».UniformProgramFamilies

/-! (Row-form version for Remark 6.20, translated from `MeasuredProgramPrefixLoci`.)
 Removing a program prefix transports the complete Gamma graph and
retains the terminal constancy test and all remaining component guards.
The prefix itself needs its component guards, without terminal constancy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t k : ℕ}

theorem gammaTransitionConstantParameterLocus_codes_iff_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) (a : Fin p → M) :
    a ∈ gammaTransitionConstantParameterLocusRow R W ↔
      ∀ (x : Fin n ⊕ Fin r → M) (y : Fin n ⊕ Fin s → M) (c : Fin qR → M)
        (x' : Fin n ⊕ Fin r → M) (y' : Fin n ⊕ Fin s → M) (c' : Fin qR → M),
        Sum.elim a (Sum.elim x y) ∈ R → Sum.elim a (Sum.elim x c) ∈ W →
        Sum.elim a (Sum.elim x' y') ∈ R → Sum.elim a (Sum.elim x' c') ∈ W →
        (∀ j : Fin s,y (.inr j)=y' (.inr j)) →
        Sum.elim a (Sum.elim x' c) ∈ W := by
  constructor
  · intro h x y c x' y' c' hR hW hR' hW' hTags
    exact h (Sum.elim x (Sum.elim y c)) (Sum.elim x' (Sum.elim y' c')) ⟨hR,hW⟩ ⟨hR',hW'⟩ hTags
  · intro h z z' hz hz' hTags
    exact h (z ∘ Sum.inl) (fun i => z (.inr (.inl i))) (fun i => z (.inr (.inr i)))
      (z' ∘ Sum.inl) (fun i => z' (.inr (.inl i))) (fun i => z' (.inr (.inr i)))
      hz.1 hz.2 hz'.1 hz'.2 hTags

/-- Removing a prefix: constancy of rows along the composite transition implies
constancy of the transported rows along the remaining transition. -/
theorem gammaTransitionConstantParameterLocus_comp_row
    (F : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (H : Set (Fin p ⊕ ((Fin n ⊕ Fin s) ⊕ (Fin n ⊕ Fin t)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) :
    gammaTransitionConstantParameterLocusRow (parameterRelationComp F H) W ⊆
      gammaTransitionConstantParameterLocusRow H (gammaTransitionImageRow F W) := by
  intro a ha
  rw [gammaTransitionConstantParameterLocus_codes_iff_row] at ha ⊢
  intro y z c y' z' c' hH hFW hH' hFW' hTags
  obtain ⟨x,hF,hW⟩ := hFW
  obtain ⟨x',hF',hW'⟩ := hFW'
  exact ⟨x',hF',ha x z c x' z' c' ⟨y,hF,hH⟩ hW ⟨y',hF',hH'⟩ hW' hTags⟩

theorem CentripetalProgramTemplate.preparedGood_comp_full_parameters_row
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (F.comp H).preparedGood A P=F.good A P ∩ H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i)) := by
  simp only [CentripetalProgramTemplate.preparedGood,CentripetalProgramTemplate.good,
    CentripetalProgramTemplate.pieceTarget_comp,Set.inter_assoc]

theorem CentripetalProgramTemplate.measuredGood_comp_row
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (F.comp H).measuredGoodRow A P W ⊆ F.good A P ∩
      H.measuredGoodRow (F.target A) (fun i => F.pieceTarget A (P i)) (W.transportRow (F.transition A)) := by
  unfold CentripetalProgramTemplate.measuredGoodRow
  rw [F.preparedGood_comp_full_parameters_row H A P]
  change (F.good A P ∩ H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i))) ∩
      gammaTransitionConstantParameterLocusRow (parameterRelationComp (F.transition A).graph (H.transition (F.target A)).graph) W.graph ⊆ _
  rintro a ⟨⟨h1,h2⟩,h3⟩
  exact ⟨h1,h2,gammaTransitionConstantParameterLocus_comp_row _ _ _ h3⟩

theorem CentripetalProgramTemplate.measuredFormGood_comp_row
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (F.comp H).measuredFormGoodRow A P W ⊆ (F.good A P ∩ F.coreFormGoodRow A W) ∩
      H.measuredFormGoodRow (F.target A) (fun i => F.pieceTarget A (P i)) (W.transportRow (F.transition A)) := by
  unfold CentripetalProgramTemplate.measuredFormGoodRow
  intro a ha
  obtain ⟨h1,h2⟩ := CentripetalProgramTemplate.measuredGood_comp_row F H A P W ha.1
  obtain ⟨h3,h4⟩ := ha.2
  exact ⟨⟨h1,h3⟩,h2,h4⟩

theorem CentripetalProgramTemplate.measuredRVTrace_afterPrefix_subset_row
    (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    ∀ D ∈ H.measuredRVTraceRow (F.target A) (fun i => F.pieceTarget A (P i)) (W.transportRow (F.transition A)),
      D ∈ (F.comp H).measuredRVTraceRow A P W := by
  intro D hD
  rcases List.mem_append.mp hD with hD | hD
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hD)))
  · have he : D=(⟨t+qR,H.gammaRVTraceRow (F.target A) (W.transportRow (F.transition A))⟩ : RVDataTemplate (M := M) S p) :=
      List.mem_singleton.mp hD
    subst D
    have hTrace : H.gammaRVTraceRow (F.target A) (W.transportRow (F.transition A))=(F.comp H).gammaRVTraceRow A W := by
      unfold CentripetalProgramTemplate.gammaRVTraceRow
      rw [W.transport_program_comp_row]
    rw [hTrace]
    exact (F.comp H).gammaRVTrace_mem_row A P W

end DiamondIntegral.Section6
