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
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
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
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowGammaTransitionSemantics

/-! (Row-form version for Remark 6.20, translated from `UniformMeasuredTerminalValues`.)
 Full terminal Gamma rows compare actual form values across different
VF parameters with the same retained base labels. Separate local terminal
constancy alone would not establish this cross-parameter conclusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}

theorem values_eq_of_transition_labels_row
    (U : UniformMeasuredProgramFamilyRow (G := G) η T A P W)
    (b c : B) (hBase : b.val.2=c.val.2)
    {Zb : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η b))}
    {Zc : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η c))}
    (f : Map (A.fibre (unaryFamilyParameter η b)) Zb) (hf : Function.Bijective f)
    (g : Map (A.fibre (unaryFamilyParameter η c)) Zc) (hg : Function.Bijective g)
    (hfb : {z | Sum.elim (unaryFamilyParameter η b) z ∈ (T.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) f.graph)
    (hgc : {z | Sum.elim (unaryFamilyParameter η c) z ∈ (T.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) g.graph)
    (x : A.fibre (unaryFamilyParameter η b)) (y : A.fibre (unaryFamilyParameter η c))
    (hTags : (f x).val.2=(g y).val.2) : (U.forms b x).val=(U.forms c y).val := by
  let ζb := (U.forms b).comp (f.inverse hf)
  let ζc := (U.forms c).comp (g.inverse hg)
  have hGraphb := gammaTransitionImage_at_row (unaryFamilyParameter η b) (T.transition A).graph W.graph f hf (U.forms b) hfb (U.graphs b)
  have hGraphc := gammaTransitionImage_at_row (unaryFamilyParameter η c) (T.transition A).graph W.graph g hg (U.forms c) hgc (U.graphs c)
  have hConstSource := (gammaTransitionConstantParameterLocus_iff_row (unaryFamilyParameter η c)
    (T.transition A).graph W.graph g (U.forms c) hgc (U.graphs c)).mp (U.admissible c).1.2
  have hConst (v w : Zc) (he : v.val.2=w.val.2) : (ζc v).val=(ζc w).val := by
    apply hConstSource (g.inverse hg v) (g.inverse hg w)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact he
  have hConstSourceB := (gammaTransitionConstantParameterLocus_iff_row (unaryFamilyParameter η b)
    (T.transition A).graph W.graph f (U.forms b) hfb (U.graphs b)).mp (U.admissible b).1.2
  have hConstB (v w : Zb) (he : v.val.2=w.val.2) : (ζb v).val=(ζb w).val := by
    apply hConstSourceB (f.inverse hf v) (f.inverse hf w)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact he
  have hRows := U.measuredRows _ (T.gammaRVTrace_mem_row A P W) b c hBase
  have h := (W.transportRow (T.transition A)).values_eq_of_rvTrace_eq_row _ _ ζb ζc hGraphb hGraphc hRows hConstB hConst (f x) (g y) hTags
  change (U.forms b (f.inverse hf (f x))).val=(U.forms c (g.inverse hg (g y))).val at h
  rw [Map.inverse_apply,Map.inverse_apply] at h
  exact h

end DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
