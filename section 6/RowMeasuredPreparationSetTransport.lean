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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
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
import «section 6».RowMeasuredPreparationTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredPreparationSetTransport`.)
 Actual measured preparations transportRow across equal source and
protected sets, with checked equality of the full actual source form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem MeasuredCoordinatePreparationRow.transport_sets_form_compatible_row
    {A C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}
    {ω : RowFormOn A qR}
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.target F.map P ω)
    (hAC : A=C) (hPQ : ∀ i,P i=Q i)
    (η : RowFormOn C qR)
    (hForm : ∀ p : A,(ω p).val=(η ⟨p.val,hAC ▸ p.property⟩).val) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) C Q hQC η,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) C T.target T.map Q η := by
  cases hAC
  let T : MeasuredCoordinatePreparationRow (G := G) A Q hQC η := (F.changeFormRow hForm).changePieces hPQ
  exact ⟨T,(hF.changeFormRow hForm).changePieces hPQ⟩

end DiamondIntegral.Section6
