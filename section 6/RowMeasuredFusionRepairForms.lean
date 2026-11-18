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
import «section 6».RowVFReindexedGammaForms
import «section 6».RowVariableApertureGammaForms
import «section 6».RowMeasuredCentripetalFusionRepairs

/-! (Row-form version for Remark 6.20, translated from `MeasuredFusionRepairForms`.)
 An actual measured fusion repair supplies both aperture form
conditions to the full measured step assembly. These conditions follow
from its guarded local components, rather than being accepted inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.MeasuredCentripetalFusionRepairRow
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : RowFormOn C qR}
variable (R : MeasuredCentripetalFusionRepairRow (G := G) η T K A P W C π σ ω)

theorem variable_core_form_constant_row (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    R.geometric.component.VariableCoreFormConstantRow R.geometric.oldRadius ω :=
  R.geometric.variable_core_form_constant_of_local_forms_row hCoeffMem R.family.forms
    (R.geometric.fibreComponents.component_core_form_constant_row h00 W R.family.forms R.family.graphs R.firstCore)
    ω R.sourceForm

theorem core_form_constant_row (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    R.geometric.component.CoreFormConstantRow ω :=
  (R.variable_core_form_constant_row h00 hCoeffMem).core_of_cutoff_row (R.geometric.oldRadius_le_global_cutoff_row hCoeffMem)

end DiamondIntegral.Section6.MeasuredCentripetalFusionRepairRow
