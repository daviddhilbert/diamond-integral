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
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowMeasuredChoiceProgramRVData
import «section 6».RowMeasuredProgramChoicePartitions
import «section 6».RowFiniteHeadFormCompatiblePrograms

/-! (Row-form version for Remark 6.20, translated from `MeasuredCoordinateProgramData`.)
 Actual coordinate-fibre witnesses yield one finite original-base
program family, a disjoint formula-choice partition and complete
separately bounded RV-data rows. Only the lower-dimensional preparation
witnesses remain an induction premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure FiniteMeasuredCoordinateProgramDataRow
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (ω : RowFormOn A qR) where
  count : ℕ
  programs : Fin count → Σ s,CentripetalProgramTemplate (M := M) S 1 (n+1) r s
  choices : Fin count → Set (Fin 1 → M)
  choices_definable : ∀ i,S.Definable LRV (choices i)
  choices_subset : ∀ i,choices i ⊆ (rawVFSpace (M := M) 1).domain ∩
    (programs i).2.measuredFormGoodRow (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplateRow ω)
  cover : ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ choices i
  disjoint : ∀ i j a,a ∈ choices i → a ∈ choices j → i=j
  geometry : ∀ i,∀ a ∈ choices i,TemplateFibreGeometry (headFibreTemplate A) (fun j => headFibreTemplate (P j)) a

def FiniteMeasuredCoordinateProgramDataRow.completeData
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : RowFormOn A qR}
    (F : FiniteMeasuredCoordinateProgramDataRow A P ω) :=
  measuredChoiceProgramRVDataRow F.programs (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) F.choices F.choices_definable

theorem FiniteMeasuredCoordinateProgramDataRow.completeData_rows_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S}
    {ω : RowFormOn A qR}
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ})
    (F : FiniteMeasuredCoordinateProgramDataRow A P ω) (a : Fin 1 → M) :
    RVValueDoublyBounded (F.completeData.fibre a).carrier :=
by
  apply measuredChoiceProgramRVData_doublyBounded_row h00 hc hκ hs hv linear hsmall hΓ F.programs (headFibreTemplate A)
    (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) F.choices F.choices_definable
      (fun i a ha => ⟨(F.choices_subset i ha).2.1.1.1,F.geometry i a ha⟩) _ a
  intro i z hz
  obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff z).mp (F.choices_subset i hz).1
  exact ⟨headGammaFormMapRow ω b,headGammaFormTemplate_section_row ω b,headGammaFormMap_levels_open_row ω b hLevels⟩

theorem exists_finite_measured_coordinate_program_data_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : RowFormOn A qR)
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparationRow (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMapRow ω a),
        FormCompatibleSynchronizedChainRow (G := G) (Fin k)
          ((headFibreTemplate A).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMapRow ω a)) :
    Nonempty (FiniteMeasuredCoordinateProgramDataRow A P ω) := by
  obtain ⟨l,T,hCover⟩ := exists_finite_head_form_compatible_programs_row h00 hc linear hκ hs hv hsmall hΓ A hARV P hPA ω hLocal
  have hRawCover (a : Fin 1 → M) (ha : a ∈ (rawVFSpace (M := M) 1).domain) :
      ∃ i,a ∈ (T i).2.measuredFormGoodRow (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplateRow ω) := by
    obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp ha
    exact hCover b
  obtain ⟨C,hC,hSub,hCCover,hDisj⟩ := exists_disjoint_measured_program_choice_row _
    ((rawVFSpace (M := M) 1).definable_domain S) (headFibreTemplate A) (fun j => headFibreTemplate (P j)) (headGammaFormTemplateRow ω) T hRawCover
  refine ⟨⟨l,T,C,hC,hSub,(fun a => hCCover _ ⟨(fun _ => a),rfl⟩),hDisj,?_⟩⟩
  intro i a ha
  obtain ⟨b,rfl⟩ := (raw_unary_vf_parameter_iff a).mp (hSub i ha).1
  exact coordinate_fibre_geometry A P hA hAD hPA hP b

end DiamondIntegral.Section6
