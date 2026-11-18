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
import «section 6».RowPromotedFormCompatiblePrograms

/-! (Row-form version for Remark 6.20, translated from `PreparedFormCompatiblePrograms`.)
 Prepared form-compatible actual chains promote to one complete
measured program, including terminal Gamma constancy and every
intermediate contracted-core form condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_prepared_form_compatible_program_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map (A.fibre a) B}
    (ω : RowFormOn (A.fibre a) qR)
    (h : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a) ω)
    (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hPA i)).image.carrier)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hConst : ∀ t u : A.fibre a,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val) :
    ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.measuredFormGoodRow A P W ∧
      {z | Sum.elim a z ∈ (T.transition A).graph}=
        (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  obtain ⟨T,ha,hCore,hGraph⟩ := exists_promoted_form_compatible_program_row h00 hc linear hκ hs hv a hsmall hΓ
    h A P W rfl (fun _ => rfl) hARV hW
  have hPreparedGood : a ∈ T.preparedGood A P := by
    refine ⟨ha,Set.mem_iInter.mpr (fun i => ?_)⟩
    apply (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph a
      ((T.pieceTarget A (P i)).fibre a) ((T.pieceTarget A (P i)).fibre_code a).symm).mpr
    have hPiece : (T.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
      mixedRelationImageTemplate_at_restriction (P i) (T.transition A).graph (T.transition A).definable
        a f (hPA i) hGraph
    rw [hPiece]
    exact hPrepared i
  exact ⟨T,⟨⟨hPreparedGood,(gammaTransitionConstantParameterLocus_iff_row a _ _ f ω hGraph hW).mpr hConst⟩,hCore⟩,hGraph⟩

end DiamondIntegral.Section6
