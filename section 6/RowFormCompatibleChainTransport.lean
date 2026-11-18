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
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowFormCompatibleSynchronizedChains

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleChainTransport`.)
 Literal source, target and protected-family transportRow for the
measured component invariant. Exact equality of the actual Gamma map
is retained when the source presentation changes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FormCompatibleSynchronizedChainRow.changeTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map A C}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : RowFormOn A qR}
    (h : FormCompatibleSynchronizedChainRow (G := G) I A B f P ω) (hBC : B=C)
    (hMap : ∀ p : A,(f p).val=(g p).val) : FormCompatibleSynchronizedChainRow (G := G) I A C g P ω := by
  cases hBC
  have he : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  rw [← he]
  exact h

theorem FormCompatibleSynchronizedChainRow.changePieces
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P Q : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : RowFormOn A qR}
    (h : FormCompatibleSynchronizedChainRow (G := G) I A B f P ω) (he : ∀ i,P i=Q i) :
    FormCompatibleSynchronizedChainRow (G := G) I A B f Q ω := by
  rw [← funext he]
  exact h

theorem FormCompatibleSynchronizedChainRow.changeSource
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {g : Map C B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : RowFormOn A qR}
    {η : RowFormOn C qR}
    (h : FormCompatibleSynchronizedChainRow (G := G) I A B f P ω) (hAC : A=C)
    (hMap : ∀ p : A,(f p).val=(g ⟨p.val,hAC ▸ p.property⟩).val)
    (hForm : ∀ p : A,(ω p).val=(η ⟨p.val,hAC ▸ p.property⟩).val) :
    FormCompatibleSynchronizedChainRow (G := G) I C B g P η := by
  cases hAC
  have hf : f=g := Map.ext (fun p => Subtype.ext (hMap p))
  have hω : ω=η := RowFormOn.ext (fun p => Subtype.ext (hForm p))
  rw [← hf,← hω]
  exact h

end DiamondIntegral.Section6
