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
import «section 6».RowMeasuredFusionRepairForms
import «section 6».RowMeasuredFusionResidualForms
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
import «section 6».RowSelectedMeasuredTerminalPreparation
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
import «section 6».RowUniformMeasuredPrefixValues
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowUniformMeasuredProgramPrefixes
import «section 6».RowUniformMeasuredTerminalValues
import «section 6».RowVFReindexedGammaForms
import «section 6».RowVariableApertureGammaForms
import «section 6».RowFusionResidualGammaGeometry

/-! (Row-form version for Remark 6.20, translated from `MeasuredFusionTerminalResidual`.)
 After a final local centripetal component, the residual is already
prepared. Full terminal Gamma rows, including comparisons between head
parameters, supply its actual measured preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.MeasuredCentripetalFusionRepairRow
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable {ω : RowFormOn C qR}
variable (R : MeasuredCentripetalFusionRepairRow (G := G) η (.centripetal K) K A P W C π σ ω)

theorem terminal_residual_preparation_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈
      (CentripetalProgramTemplate.centripetal K).rvTrace A P) :
    ∃ F : MeasuredCoordinatePreparationRow (G := G) (R.geometric.residualTarget hCoeffMem)
        (R.geometric.residualPiece hCoeffMem) (R.geometric.residualPiece_subset hCoeffMem)
        (R.geometric.fusionResidualGammaMapRow h00 hCoeffMem ω),
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) (R.geometric.residualTarget hCoeffMem) F.target F.map
        (R.geometric.residualPiece hCoeffMem) (R.geometric.fusionResidualGammaMapRow h00 hCoeffMem ω) := by
  let Y := R.geometric.residualContext h00 hc hκ hs hv hCoeffMem
  let J := Y.finish (G := G) hBRP R.family.toUniformProgramFamily.prepared_target_fibres
    (fun i => R.family.rows _ ((CentripetalProgramTemplate.centripetal K).terminal_piece_data_mem A P i))
  let Ω := R.geometric.fusionResidualGammaMapRow h00 hCoeffMem ω
  have hPhi : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (R.geometric.residualTarget hCoeffMem)
      J.target J.map
      (fun i => rvLabelPullback (R.geometric.residualTarget hCoeffMem)
        (Fin.addCases (centripetalBaseLabels R.geometric.component π) (centripetalLocalLabels R.geometric.component σ))
        (unaryIndexedMixedFamily R.geometric.parameter ((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)))) Ω :=
    .identity _ Y.proper _ (fun i => rvLabelPullback_subset _ _ _) Y.piecesProper Ω
  obtain ⟨F,hF⟩ := J.measured_form_compatible_target_row h00 hc hκ hs hv Ω hPhi (by
    intro z w hTags
    change z.val.2=w.val.2 at hTags
    obtain ⟨p,hp⟩ := R.geometric.stage_preimage ⟨z.val,z.property.1⟩
    obtain ⟨q,hq⟩ := R.geometric.stage_preimage ⟨w.val,w.property.1⟩
    let b := R.geometric.context.baseMap p
    let c := R.geometric.context.baseMap q
    let x := R.geometric.localSourcePointRow p
    let y := R.geometric.localSourcePointRow q
    have hBase : b.val.2=c.val.2 := by
      change (R.geometric.context.baseMap p).val.2=(R.geometric.context.baseMap q).val.2
      rw [← R.geometric.residual_baseMap_at_preimage_row h00 hc hκ hs hv hCoeffMem z p hp,
        ← R.geometric.residual_baseMap_at_preimage_row h00 hc hκ hs hv hCoeffMem w q hq]
      exact Y.baseMap_labels z w hTags
    have hLocalTags : ((R.geometric.fibreComponents.component b).bijection x).val.2=
        ((R.geometric.fibreComponents.component c).bijection y).val.2 := by
      have h := congrArg (fun u => u ∘ centripetalLocalLabels R.geometric.component σ) hTags
      have hz := R.geometric.residual_local_at_preimage_row h00 hCoeffMem z p hp
      have hw := R.geometric.residual_local_at_preimage_row h00 hCoeffMem w q hq
      exact (congrArg Prod.snd hz).symm.trans (h.trans (congrArg Prod.snd hw))
    have hValue := R.family.values_eq_of_transition_labels_row b c hBase
      (R.geometric.fibreComponents.component b).bijection ((R.geometric.fibreComponents.component b).bijective h00)
      (R.geometric.fibreComponents.component c).bijection ((R.geometric.fibreComponents.component c).bijective h00)
      (R.geometric.fibreComponents.component_transition_graph_row b) (R.geometric.fibreComponents.component_transition_graph_row c)
      x y hLocalTags
    have hSource := (R.sourceForm p).symm.trans ((rowFormExtension_at (R.family.forms b) x).trans
      (hValue.trans ((rowFormExtension_at (R.family.forms c) y).symm.trans (R.sourceForm q))))
    exact (R.geometric.fusionResidualGammaMap_at_preimage_row h00 hCoeffMem ω z p hp).trans
      (hSource.trans (R.geometric.fusionResidualGammaMap_at_preimage_row h00 hCoeffMem ω w q hq).symm))
  exact ⟨F.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i),
    hF.changePieces (fun i => R.geometric.residual_piece_eq h00 hCoeffMem i)⟩

end DiamondIntegral.Section6.MeasuredCentripetalFusionRepairRow
