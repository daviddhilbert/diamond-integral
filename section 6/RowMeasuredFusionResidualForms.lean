import «section 6».RowApertureCoordinateGammaForms
import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedCoreFormCompatibility
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaConstancy
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFiniteMeasuredCentripetalPrograms
import «section 6».RowFormCompatibleCarriedCertificates
import «section 6».RowFormCompatibleCarriedPreparation
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleFocusSteps
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleTagBranchAssembly
import «section 6».RowFormCompatibleTagChainExtensions
import «section 6».RowFormCompatibleTagComponents
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowFrozenSelectedGammaAgreement
import «section 6».RowFusionCoreFormConstancy
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
import «section 6».RowMeasuredBranchFormConstancy
import «section 6».RowMeasuredCentripetalFusionRepairs
import «section 6».RowMeasuredCentripetalProgramRealizations
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredComplementaryBranchPreparation
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredCoreDimensionInduction
import «section 6».RowMeasuredFormCompatibleCarrying
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredFusionStepAssembly
import «section 6».RowMeasuredIndexedFocusRepair
import «section 6».RowMeasuredPermutedCoordinateBundles
import «section 6».RowMeasuredPreparationSetTransport
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProgramPrefixLoci
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredRVRefinementPreparation
import «section 6».RowMeasuredSelectedIndexedFocusRepair
import «section 6».RowMeasuredSynchronizedTargets
import «section 6».RowMeasuredUnaryBaseFocusFreezing
import «section 6».RowMeasuredVFConjugatedPreparation
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowMeasuredVariableReleaseInduction
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedMeasuredProgramRealizations
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaDescent
import «section 6».RowRVRefinementGammaForms
import «section 6».RowRVRefinementGammaProducts
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSelectedGammaFormDescent
import «section 6».RowSemanticGammaBranchDescent
import «section 6».RowSequentialMeasuredCentripetalPrograms
import «section 6».RowSpecialGammaTransport
import «section 6».RowTemplateComponentGammaGuards
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
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowUniformMeasuredProgramPrefixes
import «section 6».RowUniformMeasuredTerminalValues
import «section 6».RowVFReindexedGammaForms
import «section 6».RowVariableApertureGammaForms
import «section 6».RowMeasuredFusionRepairForms
import «section 6».RowUniformMeasuredPrefixValues
import «section 6».RowSelectedMeasuredTerminalPreparation

/-! (Row-form version for Remark 6.20, translated from `MeasuredFusionResidualForms`.)
 The actual residual source retains the unary base and realizes the
old local component on its full selected point. Its actual inverse
transported form therefore agrees with the remaining measured family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}

namespace CentripetalFusionRepair
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

theorem residual_baseMap_at_preimage_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (z : R.residualTarget hCoeffMem) (p : C) (hp : (R.stageMap p).val=z.val) :
    (R.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z=R.context.baseMap p := by
  apply Subtype.ext
  rw [SelectedProgramContext.baseMap_value,SelectedProgramContext.baseMap_value,← hp,R.stageMap_value]
  exact centripetal_selected_base R.component K.coordinate R.coordinate π p.val

theorem residual_local_at_preimage_row
    (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (z : R.residualTarget hCoeffMem) (p : C) (hp : (R.stageMap p).val=z.val) :
    (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.component σ)=
      (R.fibreComponents.component (R.context.baseMap p)).point (Fin.tail p.val.1,p.val.2 ∘ σ) := by
  have hRes : (R.stageMap p).val.2 ∈ (R.residualTags hCoeffMem).carrier := hp.symm ▸ z.property.2
  have hOld := (R.residualTags_at h00 hCoeffMem p).mp hRes
  rw [← hp,R.stageMap_value]
  exact centripetal_selected_local_point R.component (R.fibreComponents.component (R.context.baseMap p)) σ p.val
    (R.coordinate.trans (congrArg Fin.succ (R.fibreComponents.coordinate _)).symm)
    (R.focus p) (R.coefficient _) hOld

end CentripetalFusionRepair

namespace MeasuredCentripetalFusionRepairRow
variable {H : CentripetalProgramTemplate (M := M) S 1 (n+1) (1+s) t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : RowFormOn C qR}
variable (R : MeasuredCentripetalFusionRepairRow (G := G) η ((CentripetalProgramTemplate.centripetal K).comp H) K A P W C π σ ω)

theorem residual_source_form_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
      ((CentripetalProgramTemplate.centripetal K).comp H).rvTrace A P) :
    ∀ z : R.geometric.residualTarget hCoeffMem,
      rowFormExtension ((R.family.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
        ((R.geometric.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z))
        (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.geometric.component σ)=
          (R.geometric.fusionResidualGammaMapRow h00 hCoeffMem ω z).val := by
  intro z
  obtain ⟨p,hp⟩ := R.geometric.stage_preimage ⟨z.val,z.property.1⟩
  let b := R.geometric.context.baseMap p
  let x := R.geometric.localSourcePointRow p
  let y : ((CentripetalProgramTemplate.centripetal K).target A).fibre
      (unaryFamilyParameter R.geometric.parameter b) :=
    ⟨(R.geometric.fibreComponents.component b).bijection x,by
      rw [R.geometric.fibreComponents.target_fibre]
      exact ((R.geometric.fibreComponents.component b).bijection x).property⟩
  have hValue := R.family.afterPrefix_value_row h00 hc linear hκ hs hv hsmall hΓ b
    (R.geometric.fibreComponents.component b).bijection
    ((R.geometric.fibreComponents.component b).bijective h00)
    (R.geometric.fibreComponents.component_transition_graph_row b) x y rfl
  have hLocal := R.geometric.residual_local_at_preimage_row h00 hCoeffMem z p hp
  have hLeft : rowFormExtension ((R.family.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
        ((R.geometric.residualContext h00 hc hκ hs hv hCoeffMem).baseMap z))
      (Fin.tail z.val.1,z.val.2 ∘ centripetalLocalLabels R.geometric.component σ)=(ω p).val := by
    rw [R.geometric.residual_baseMap_at_preimage_row h00 hc hκ hs hv hCoeffMem z p hp,hLocal]
    exact (rowFormExtension_at _ y).trans (hValue.trans
      ((rowFormExtension_at (R.family.forms b) x).symm.trans (R.sourceForm p)))
  have hAt : (R.geometric.fusionResidualGammaMapRow h00 hCoeffMem ω z).val=(ω p).val := by
    change (R.geometric.fusionGammaMapRow h00 ω ⟨z.val,z.property.1⟩).val=(ω p).val
    have he : (⟨z.val,z.property.1⟩ : R.geometric.stageTarget)=R.geometric.stageMap p := Subtype.ext hp.symm
    rw [he]
    exact R.geometric.fusionGammaMap_transport_row h00 ω p
  exact hLeft.trans hAt.symm

end MeasuredCentripetalFusionRepairRow
end DiamondIntegral.Section6
