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
import «section 6».RowMeasuredFormCompatibleTargets

/-! (Row-form version for Remark 6.20, translated from `MeasuredPreparationTransport`.)
 Literal protected-family and source-form changes for actual measured
preparations. The underlying maps and all prepared images are retained. -/

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
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {P Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {hPA : ∀ i,(P i).carrier ⊆ A.carrier} {hQA : ∀ i,(Q i).carrier ⊆ A.carrier}
variable {ω η : RowFormOn A qR}

def MeasuredCoordinatePreparationRow.toPreparedSynchronizedRow
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω)
    (h : SynchronizedCentripetalChain (G := G) (Fin k) A F.target F.map P) :
    PreparedSynchronizedFamily (G := G) A P hPA :=
  ⟨F.arity,F.target,F.map,h,F.proper,F.doublyBounded,F.prepared,fun i => (F.pieces i).2⟩

def MeasuredCoordinatePreparationRow.changePieces
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω) (he : ∀ i,P i=Q i) :
    MeasuredCoordinatePreparationRow (G := G) A Q hQA ω := {
  arity := F.arity
  target := F.target
  map := F.map
  special := F.special
  proper := F.proper
  doublyBounded := F.doublyBounded
  prepared := F.prepared
  tagged := F.tagged
  form := F.form
  transportRow := F.transportRow
  constant := F.constant
  pieces := by
    intro i
    have h := funext he
    cases h
    exact F.pieces i }

def MeasuredCoordinatePreparationRow.changeFormRow
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω)
    (he : ∀ p : A,(ω p).val=(η p).val) : MeasuredCoordinatePreparationRow (G := G) A P hPA η := {
  arity := F.arity
  target := F.target
  map := F.map
  special := F.special
  proper := F.proper
  doublyBounded := F.doublyBounded
  prepared := F.prepared
  tagged := F.tagged
  form := F.form
  transportRow := fun p => (F.transportRow p).trans (he p)
  constant := F.constant
  pieces := F.pieces }

theorem FormCompatibleSynchronizedChainRow.changeFormRow {s : ℕ}
    {B : DefSet (rawMixedSpace (M := M) (n+1) s) S} {f : Map A B}
    (h : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A B f P ω)
    (he : ∀ p : A,(ω p).val=(η p).val) :
    FormCompatibleSynchronizedChainRow (G := G) (Fin k) A B f P η :=
  h.changeSource rfl (fun _ => rfl) he

end DiamondIntegral.Section6
