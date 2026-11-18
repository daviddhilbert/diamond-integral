import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
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
import «section 6».RowCoreFormCompatibility
import «section 6».SynchronizedFocusSteps

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleSynchronizedChains`.)
 The measured dimension-induction invariant retains the complete
common permitted chain and, at each centripetal component, constancy of
the current actual form on its contracted coordinate fibres. Intermediate
forms have exact transportRow; this is stronger than terminal constancy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive FormCompatibleSynchronizedChainRow (I : Type*) : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    (I → DefSet (rawMixedSpace (M := M) n r) S) →
    RowFormOn A qR → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier)
      (ω : RowFormOn A qR) :
      FormCompatibleSynchronizedChainRow I A A (Map.id A) P ω
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier) (hPD : ∀ i,VFDoublyBounded (P i).carrier)
      (ω : RowFormOn A qR) :
      FormCompatibleSynchronizedChainRow I A (regularizeMap A).image (regularization A) P ω
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (E : ∀ i,CentripetalData (G := G) (P i)) (hData : ∀ i,ApertureRestrictionData D (E i))
      (ω : RowFormOn A qR) (hForm : D.CoreFormConstantRow ω) :
      FormCompatibleSynchronizedChainRow I A D.map.image D.bijection P ω
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C}
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      {ω : RowFormOn A qR}
      (hf : FormCompatibleSynchronizedChainRow I A B f P ω)
      (η : RowFormOn B qR)
      (hTransport : ∀ p : A,(η (f p)).val=(ω p).val)
      (hg : FormCompatibleSynchronizedChainRow I B C g (fun i => (f.restrict (hPA i)).image) η) :
      FormCompatibleSynchronizedChainRow I A C (g.comp f) P ω

variable {r s : ℕ}

theorem FormCompatibleSynchronizedChainRow.toSynchronizedRow {I : Type*}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : RowFormOn A qR}
    (h : FormCompatibleSynchronizedChainRow (G := G) I A B f P ω) :
    SynchronizedCentripetalChain (G := G) I A B f P := by
  induction h with
  | identity A hA P hPA hP ω => exact .identity A hA P hPA hP
  | regularize A hA hAD P hPA hP hPD ω => exact .regularize A hA hAD P hPA hP hPD
  | centripetal A D P hPA E hData ω hForm => exact .centripetal A D P hPA E hData
  | comp P hPA hf η hTransport hg ihf ihg => exact .comp P hPA ihf ihg

end DiamondIntegral.Section6
