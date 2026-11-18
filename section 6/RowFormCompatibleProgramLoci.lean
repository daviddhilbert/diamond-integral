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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowGammaCoreComponentSemantics

/-! (Row-form version for Remark 6.20, translated from `FormCompatibleProgramLoci`.)
 Whole-program admissibility includes core-form compatibility at
every actual centripetal stage. Intermediate Gamma graphs are transported
by the full transition, and the resulting test is original-base definable. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s k : ℕ}

namespace CentripetalProgramTemplate

def coreFormGoodRow : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    MixedSetParameterTemplate (M := M) S p n r → GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r → Set (Fin p → M)
  | _,_,.identity _,_,_ => Set.univ
  | _,_,.regularize _,_,_ => Set.univ
  | r,_,.centripetal T,A,W =>
      gammaCoreConstantParameterLocusRow (focusComponentTransition T A) W.graph T.coordinate (Fin.castAdd r (0 : Fin 1))
  | _,_,.comp F H,A,W => F.coreFormGoodRow A W ∩ H.coreFormGoodRow (F.target A) (W.transportRow (F.transition A))

theorem coreFormGood_definable_row (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    S.Definable LRV (T.coreFormGoodRow A W) := by
  induction T with
  | identity r => exact Set.definable_univ
  | regularize r => exact Set.definable_univ
  | centripetal T =>
    exact gammaCoreConstantParameterLocus_definable_row (focusComponentTransition T A) W.graph
      (focusComponentTransition_definable T A) W.definable T.coordinate _
  | comp F H ihF ihH => exact (ihF A W).inter (ihH (F.target A) (W.transportRow (F.transition A)))

def measuredFormGoodRow (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : Set (Fin p → M) :=
  T.measuredGoodRow A P W ∩ T.coreFormGoodRow A W

theorem measuredFormGood_definable_row (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : S.Definable LRV (T.measuredFormGoodRow A P W) :=
  (T.measuredGood_definable_row A P W).inter (T.coreFormGood_definable_row A W)

end CentripetalProgramTemplate

theorem gammaCoreConstantParameterLocus_substitute_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (h : DefinableParameterSubstitution (M := M) S p q) (j : Fin n) (coreTag : Fin s) :
    gammaCoreConstantParameterLocusRow (parameterSubstitution h R) (parameterSubstitution h W) j coreTag=
      h.value ⁻¹' gammaCoreConstantParameterLocusRow R W j coreTag := by
  ext a
  rfl

theorem CentripetalProgramTemplate.substitute_coreFormGood_row
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (T.substitute h).coreFormGoodRow (A.substitute h) (W.substitute h)=h.value ⁻¹' T.coreFormGoodRow A W := by
  induction T with
  | identity r => rfl
  | regularize r => rfl
  | centripetal T =>
    change gammaCoreConstantParameterLocusRow (focusComponentTransition (T.substitute h) (A.substitute h))
      (parameterSubstitution h W.graph) _ _=_
    rw [focusComponentTransition_substitute]
    exact gammaCoreConstantParameterLocus_substitute_row _ _ h _ _
  | comp F H ihF ihH =>
    have hTransport := W.transport_substitute_row (F.transition A)
      ((F.substitute h).transition (A.substitute h)) h (F.substitute_transition h A)
    change (F.substitute h).coreFormGoodRow (A.substitute h) (W.substitute h) ∩
      (H.substitute h).coreFormGoodRow ((F.substitute h).target (A.substitute h))
        ((W.substitute h).transportRow ((F.substitute h).transition (A.substitute h)))=_
    rw [← hTransport,F.substitute_target h A,ihF A W,ihH (F.target A) (W.transportRow (F.transition A))]
    rfl

end DiamondIntegral.Section6
