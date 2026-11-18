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
import «section 6».RowGammaTransitionSemantics
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
import «section 6».RowMeasuredProgramPrefixLoci
import «section 6».RowExactGammaTransport

/-! (Row-form version for Remark 6.20, translated from `UniformMeasuredProgramPrefixes`.)
 Removing an actual program prefix constructs the remaining local
Gamma maps through its actual inverse. Full graphs, open levels, all
remaining component guards and the complete measured row bound survive. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t v k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def afterPrefix
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {F : CentripetalProgramTemplate (M := M) S 1 n s t}
    {H : CentripetalProgramTemplate (M := M) S 1 n t v}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
    (U : UniformMeasuredProgramFamilyRow (G := G) η (F.comp H) A P W) :
    UniformMeasuredProgramFamilyRow (G := G) η H (F.target A) (fun i => F.pieceTarget A (P i)) (W.transportRow (F.transition A)) := by
  have hGuard (b : B) := F.measuredFormGood_comp_row H A P W (U.admissible b)
  have hReal (b : B) := F.exists_realization h00 hc hκ hs hv A P _ (hGuard b).1.1
    (U.geometry b).proper (U.geometry b).doublyBounded (U.geometry b).subset (U.geometry b).piecesProper
  let R (b : B) := Classical.choice (hReal b)
  let ζ (b : B) := (U.forms b).comp ((R b).map.inverse ((R b).chain.toChain.toSpecial.bijective h00))
  have hTransport (b : B) (p : A.fibre (unaryFamilyParameter η b)) :
      (ζ b ((R b).map p)).val=(U.forms b p).val := by
    change (U.forms b ((R b).map.inverse _ ((R b).map p))).val=(U.forms b p).val
    rw [Map.inverse_apply]
  refine {
    toUniformProgramFamily := U.toUniformProgramFamily.afterPrefix (G := G) h00 hc hκ hs hv
    forms := ζ
    graphs := ?_
    levels := ?_
    admissible := fun b => (hGuard b).2
    measuredRows := fun D hD => U.measuredRows D (F.measuredRVTrace_afterPrefix_subset_row H A P W D hD)
    measuredBound := fun D hD => U.measuredBound D (F.measuredRVTrace_afterPrefix_subset_row H A P W D hD) }
  · intro b
    exact gammaTransitionImage_at_row (unaryFamilyParameter η b) (F.transition A).graph W.graph (R b).map
      ((R b).chain.toChain.toSpecial.bijective h00) (U.forms b) (R b).graph (U.graphs b)
  · intro b
    exact (R b).chain.toChain.toSpecial.exact_gamma_levels_open_row h00 hc linear hκ hs hv
      (small_union_range hκ.le S hsmall (unaryFamilyParameter η b))
      (hΓ.mono Set.subset_union_left (Set.Subset.rfl)) (U.forms b) (U.levels b) (ζ b) (hTransport b)

end DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
