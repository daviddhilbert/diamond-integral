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
import «section 6».RowGammaFormUniformFibres
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
import «section 6».RowFormCompatibleProgramLoci

/-! (Row-form version for Remark 6.20, translated from `MeasuredProgramChoicePartitions`.)
 The finite formula-choice cover for complete programs has a
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
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k l : ℕ}

theorem exists_disjoint_measured_program_choice_row
    (X : Set (Fin p → M)) (hX : S.Definable LRV X)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s)
    (hCover : ∀ a ∈ X,∃ i,a ∈ (T i).2.measuredFormGoodRow A P W) :
    ∃ C : Fin l → Set (Fin p → M),(∀ i,S.Definable LRV (C i)) ∧
      (∀ i,C i ⊆ X ∩ (T i).2.measuredFormGoodRow A P W) ∧
      (∀ a ∈ X,∃ i,a ∈ C i) ∧ (∀ i j a,a ∈ C i → a ∈ C j → i=j) := by
  let earlier (i : Fin l) : Set (Fin p → M) :=
    ⋃ j : {j : Fin l // j < i},(T j.val).2.measuredFormGoodRow A P W
  let C (i : Fin l) := (X ∩ (T i).2.measuredFormGoodRow A P W) \ earlier i
  have hEarlier (i) : S.Definable LRV (earlier i) :=
    Set.definable_iUnion_of_finite (fun j => (T j.val).2.measuredFormGood_definable_row A P W)
  have memEarlier (i : Fin l) (a : Fin p → M) : a ∈ earlier i ↔
      ∃ j,j < i ∧ a ∈ (T j).2.measuredFormGoodRow A P W := by
    simp only [earlier,Set.mem_iUnion,Subtype.exists,exists_prop]
  refine ⟨C,(fun i => (hX.inter ((T i).2.measuredFormGood_definable_row A P W)).sdiff (hEarlier i)),
    (fun _ => Set.sdiff_subset),?_,?_⟩
  · intro a ha
    let I := Finset.univ.filter (fun i => a ∈ (T i).2.measuredFormGoodRow A P W)
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
