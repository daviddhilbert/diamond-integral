import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».CentripetalProgramSubstitution

/-! (Row-form version for Remark 6.20, translated from `MeasuredProgramSubstitution`.)
 Definable freezing or reparametrization transports the whole
Gamma graph and the measured terminal test together with the complete
finite program. No level value is added to the parameter base. -/

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

def GammaFormParameterTemplateRow.substitute (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) : GammaFormParameterTemplateRow (qR := qR) (M := M) S q n r :=
  ⟨parameterSubstitution h W.graph,parameterSubstitution_definable h _ W.definable⟩

theorem GammaFormParameterTemplateRow.substitute_section_row (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) (a : Fin q → M) :
    {z | Sum.elim a z ∈ (W.substitute h).graph}={z | Sum.elim (h.value a) z ∈ W.graph} := rfl

theorem gammaTransitionConstantParameterLocus_substitute_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (h : DefinableParameterSubstitution (M := M) S p q) :
    gammaTransitionConstantParameterLocusRow (parameterSubstitution h R) (parameterSubstitution h W)=
      h.value ⁻¹' gammaTransitionConstantParameterLocusRow R W := by
  ext a
  rfl

theorem CentripetalProgramTemplate.substitute_measuredGood_row
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (T.substitute h).measuredGoodRow (A.substitute h) (fun i => (P i).substitute h) (W.substitute h)=
      h.value ⁻¹' T.measuredGoodRow A P W := by
  unfold CentripetalProgramTemplate.measuredGoodRow
  rw [T.substitute_preparedGood h A P,T.substitute_transition h A]
  rw [show (W.substitute h).graph=parameterSubstitution h W.graph from rfl]
  rw [gammaTransitionConstantParameterLocus_substitute_row]
  rfl

end DiamondIntegral.Section6
