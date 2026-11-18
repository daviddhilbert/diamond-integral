import «section 6».RowArbitraryCoordinateBranches
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
import «section 6».RowFormCompatibleChainTransport
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
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProgramPrefixLoci
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSelectedMeasuredRegularizationTerminal
import «section 6».RowSelectedMeasuredTerminalPreparation
import «section 6».RowSequentialMeasuredCentripetalPrograms
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
import «section 6».RowUniformMeasuredPrefixValues
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowUniformMeasuredProgramPrefixes
import «section 6».RowUniformMeasuredTerminalValues
import «section 6».RowMeasuredSelectedProgramPrefixes

/-! (Row-form version for Remark 6.20, translated from `MeasuredSelectedRegularizationAssembly`.)
 A measured preparation after global regularization precomposes
with its literal protected images and retains the component form chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem precompose_measured_regularization_row
    (h00 : M ⊨ Axioms.ACVF00)
    (X : SelectedProgramContext η A P C π σ)
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier)
    (ω : RowFormOn C qR)
    (F : MeasuredCoordinatePreparationRow (G := G) (regularizeMap C).image
      (fun i => rvLabelPullback (regularizeMap C).image
        (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
        (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i))))
      (fun i => rvLabelPullback_subset _ _ _) (regularizationGammaFormRow ω))
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (regularizeMap C).image F.target F.map
      (fun i => rvLabelPullback (regularizeMap C).image
        (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
        (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i))))
      (regularizationGammaFormRow ω)) :
    ∃ J : MeasuredCoordinatePreparationRow (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) C J.target J.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let Q (i) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))
  have hQC (i) : (Q i).carrier ⊆ C.carrier := rvLabelPullback_subset C _ _
  have hImages (i) : ((regularization C).restrict (hQC i)).image.carrier ⊆ (regularizeMap C).image.carrier := by
    rintro z ⟨p,hp⟩
    exact hp ▸ ((regularization C).restrict (hQC i) p).property
  let F' : MeasuredCoordinatePreparationRow (G := G) (regularizeMap C).image
      (fun i => ((regularization C).restrict (hQC i)).image) hImages (regularizationGammaFormRow ω) :=
    F.changePieces (fun i => regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base)
  have hF' : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (regularizeMap C).image F'.target F'.map
      (fun i => ((regularization C).restrict (hQC i)).image) (regularizationGammaFormRow ω) :=
    hF.changePieces (fun i => regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base)
  have hStage : SynchronizedCentripetalChain (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i))
  have hPhi : FormCompatibleSynchronizedChainRow (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q ω :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i)) ω
  let J := MeasuredCoordinatePreparationRow.precompose h00 Q hQC (regularization C) hStage.toChain.toSpecial
    (fun i => ((hStage.atPiece i).literal_restriction h00 (hQC i))) hImages ω (regularizationGammaFormRow ω)
    (regularizationGammaForm_transport_row ω) F'
  exact ⟨J,.comp Q hQC hPhi (regularizationGammaFormRow ω) (regularizationGammaForm_transport_row ω) hF'⟩

end DiamondIntegral.Section6.SelectedProgramContext
