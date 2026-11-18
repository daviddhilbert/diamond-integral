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
import «section 6».RowGammaCoreComponentSemantics
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
import «section 6».TemplateComponentFamilies
import «section 6».RowFormCompatibleProgramLoci

/-! (Row-form version for Remark 6.20, translated from `TemplateComponentGammaGuards`.)
 The actual local components of a template family satisfy its full
Gamma-core guard. Their coordinate, coefficient, active tags and complete
focus graph identify the literal transition used by the first-order test. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.TemplateComponentFamily
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P}

theorem component_transition_graph_row (L : TemplateComponentFamily (G := G) η T A P hGood) (b : B) :
    {z | Sum.elim (unaryFamilyParameter η b) z ∈ focusComponentTransition T A}=
      (rawMixedSpace n s).relation (rawMixedSpace n (1+s)) (L.component b).bijection.graph :=
  focusComponentTransition_at T A _ (hGood b).1.1.1 (hGood b).1.1.2 (L.component b)
    (L.coordinate b) (L.active b) (L.coefficient b) (L.focus b)

theorem component_core_form_constant_row
    (L : TemplateComponentFamily (G := G) η T A P hGood) (h00 : M ⊨ Axioms.ACVF00)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (hGraph : ∀ b,{z | Sum.elim (unaryFamilyParameter η b) z ∈ W.graph}=
      (rawMixedSpace n s).relation (rawRVSpace (M := M) qR) (ζ b).graph)
    (hGuard : ∀ b,unaryFamilyParameter η b ∈ (CentripetalProgramTemplate.centripetal T).coreFormGoodRow A W) (b : B) :
    (L.component b).CoreFormConstantRow (ζ b) := by
  have h := hGuard b
  change unaryFamilyParameter η b ∈ gammaCoreConstantParameterLocusRow (focusComponentTransition T A) W.graph T.coordinate _ at h
  rw [← L.coordinate b] at h
  exact (gammaCoreConstantParameterLocus_at_component_row _ _ _ (L.component b) h00 (ζ b)
    (L.component_transition_graph_row b) (hGraph b)).mp h

end DiamondIntegral.Section6.TemplateComponentFamily
