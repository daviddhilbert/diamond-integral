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
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowHeadGammaFormMaps
import «section 6».RowHeadGammaFormTemplates
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowFiniteFormCompatiblePrograms
import «section 6».RowFiniteHeadMeasuredPrograms

/-! (Row-form version for Remark 6.20, translated from `FiniteHeadFormCompatiblePrograms`.)
 Measured head-fibre preparation with the component form invariant
supplies finitely many original-base programs retaining that invariant
at every stage, as well as all terminal measured conclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_head_form_compatible_programs_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (ω : RowFormOn A qR)
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparationRow (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMapRow ω a),
        FormCompatibleSynchronizedChainRow (G := G) (Fin k)
          ((headFibreTemplate A).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMapRow ω a)) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S 1 (n+1) r s,
      ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ (T i).2.measuredFormGoodRow
        (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) := by
  obtain ⟨l,T,hCover⟩ := exists_finite_form_compatible_programs_row h00 hc linear hκ hs hv hsmall hΓ
    (rawVFSpace (M := M) 1).domain ((rawVFSpace (M := M) 1).definable_domain S)
    (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) (by
      intro z hz
      obtain ⟨a,rfl⟩ := (raw_unary_vf_parameter_iff z).mp hz
      obtain ⟨F,hF⟩ := hLocal a
      refine ⟨F.arity,F.target,F.map,headGammaFormMapRow ω a,hF,headFibreTemplate_rvPullback A hARV a,
        (fun i => (F.pieces i).2),headGammaFormTemplate_section_row ω a,?_⟩
      intro t u he
      have h := F.constant (F.map t).val (F.map t).property (F.map u).val (F.map u).property he
      rw [rowFormExtension_at F.form (F.map t),rowFormExtension_at F.form (F.map u)] at h
      exact (F.transportRow t).symm.trans (h.trans (F.transportRow u)))
  exact ⟨l,T,fun a => hCover (fun _ => a.val) ⟨(fun _ => a),rfl⟩⟩

end DiamondIntegral.Section6
