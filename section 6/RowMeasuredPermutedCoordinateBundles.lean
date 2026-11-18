import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedCoreFormCompatibility
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
import «section 6».RowFormCompatibleCarriedCertificates
import «section 6».RowFormCompatibleCarriedPreparation
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramRealizations
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredSynchronizedTargets
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedMeasuredProgramRealizations
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaForms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSemanticGammaBranchDescent
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
import «section 6».RowVFReindexedGammaForms
import «section 6».RowMeasuredVFConjugatedPreparation
import «section 6».RowMeasuredFormCompatibleCarrying
import «section 6».RowCoordinateGammaConstancy

/-! (Row-form version for Remark 6.20, translated from `MeasuredPermutedCoordinateBundles`.)
 Actual projected measured preparation carries through a full VF
disc in any coordinate, then conjugates to an actual permitted chain
in the original coordinates with the original form unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_coordinate_bundle_of_projected_preparation_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hW : ProperInvariant S W.carrier) (hD : VFDoublyBounded W.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S) (hPW : ∀ i,(P i).carrier ⊆ W.carrier)
    (e : Fin (n+2) ≃ Fin (n+2)) (j : Fin r)
    (hBundle : (reindexedVFSet W e).carrier=(rvCoordinateBundle (coordinateProjection W e) j).carrier)
    (hPieces : ∀ i,(reindexedVFSet (P i) e).carrier=
      (rvCoordinateBundle (coordinateProjection (P i) e) j).carrier)
    (ω : RowFormOn W qR)
    (η : RowFormOn (coordinateProjection W e) qR)
    (hη : ∀ q : reindexedVFSet W e,η ((vfDropLast (reindexedVFSet W e)).toImage q)=reindexedGammaFormRow ω e q)
    (F : MeasuredCoordinatePreparationRow (G := G) (coordinateProjection W e)
      (fun i => coordinateProjection (P i) e) (fun i => coordinateProjection_subset (hPW i) e) η)
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (coordinateProjection W e) F.target F.map
      (fun i => coordinateProjection (P i) e) η) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) W P hPW ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) W T.target T.map P ω := by
  obtain ⟨T,hT,hFixed⟩ := measured_form_compatible_preparation_carrying_coordinate_row h00 hc hκ hs hv
    (coordinateProjection_properInvariant W e hW) (coordinateProjection_doublyBounded W e hD) F hF
    j (reindexedVFSet W e) (fun i => reindexedVFSet (P i) e)
    (fun i q hq => (mem_reindexedVFSet W e q).mpr (hPW i ((mem_reindexedVFSet (P i) e q).mp hq)))
    hBundle hPieces (reindexedGammaFormRow ω e) (by
      intro q
      exact (rowFormExtension_at η ((vfDropLast (reindexedVFSet W e)).toImage q)).trans
        (congrArg Subtype.val (hη q)))
  exact measured_preparation_conjugate_vf_coordinates_row h00 hc hκ hs hv hW hD e P hPW ω T hT

end DiamondIntegral.Section6
