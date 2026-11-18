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
import «section 6».RowFormCompatibleFocusSteps
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
import «section 6».RowMeasuredCoordinateProgramData
import «section 6».RowMeasuredFrozenUnaryRVDataPreparation
import «section 6».RowMeasuredFrozenUnaryRVTemplatePreparation
import «section 6».RowMeasuredProgramChoicePartitions
import «section 6».RowMeasuredProgramGeometricData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredProtectedUnaryDataFreezing
import «section 6».RowMeasuredUnaryContextSteps
import «section 6».RowMeasuredUnaryValueContextPreparation
import «section 6».RowMeasuredUnaryValueContextStep
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
import «section 6».RowFrozenMeasuredCoordinateProgramData

/-! (Row-form version for Remark 6.20, translated from `FrozenMeasuredGeometricData`.)
 The actual measured frozen family retains all existing geometric
program data, with exactly the same unary map and ambient lift. Freezing
also leaves the actual full Gamma form unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : RowFormOn X.source qR}
namespace FrozenMeasuredCoordinateProgramDataRow

def forget (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) :
    FrozenCoordinateProgramData (G := G) A C hCA X P := {
  programs := F.programs.forget
  unary := {
    freezing := F.unary.freezing
    arity := F.unary.arity
    target := F.unary.target
    map := F.unary.map
    chain := F.unary.chain
    proper := F.unary.proper
    doublyBounded := F.unary.doublyBounded
    pullback := F.unary.pullback
    tagged := F.unary.tagged
    pieces := F.unary.pieces
    lift := ⟨F.unary.lift⟩
    ambientProduct := F.unary.ambientProduct
    protectedProducts := F.unary.protectedProducts
    unaryProducts := F.unary.unaryProducts
    data := fun p q he => geometric_data_eq_of_measured_data_eq_row h00 F.programs.programs
      (headFibreTemplate X.source) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω)
      F.programs.choices F.programs.choices_definable _ _ (F.unary.data p q he) } }

theorem frozen_gamma_equal_row
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) :
    FMT.frozenGammaFormRow F.unary.freezing.balls F.unary.freezing.centers (0 : Fin (n+2))
      F.unary.freezing.separated F.unary.freezing.balls_definable F.unary.freezing.centers_definable
      F.unary.ambientProduct ω=ω :=
  FMT.frozenGammaForm_eq_row _ _ _ _ _ _ _ ω F.unary.formProducts

end FrozenMeasuredCoordinateProgramDataRow
end DiamondIntegral.Section6
