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
import «section 6».RowGammaTransitionSemantics

/-! (Row-form version for Remark 6.20, translated from `MeasuredCentripetalProgramTemplates`.)
 Whole-program measured preparation has one original-base definable
parameter test, including full Gamma-code graphs. Actual simultaneous
prepared maps promote to this test without adding Gamma names. -/

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

structure GammaFormParameterTemplateRow (S : Set M) (p n r : ℕ) where
  graph : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)
  definable : S.Definable LRV graph

theorem exists_promoted_gamma_form_template_row (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : RowFormOn A qR) :
    ∃ W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r,
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a
    ((rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) ω.graph_definable
  refine ⟨⟨{z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R},hR⟩,?_⟩
  ext z
  exact Set.ext_iff.mp hSection z

def CentripetalProgramTemplate.measuredGoodRow
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : Set (Fin p → M) :=
  T.preparedGood A P ∩ gammaTransitionConstantParameterLocusRow (T.transition A).graph W.graph

theorem CentripetalProgramTemplate.measuredGood_definable_row
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) : S.Definable LRV (T.measuredGoodRow A P W) :=
  (T.preparedGood_definable A P).inter
    (gammaTransitionConstantParameterLocus_definable_row _ _ (T.transition A).definable W.definable)

theorem exists_promoted_measured_centripetal_program_row
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
    (h : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a))
    (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hPA i)).image.carrier)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hConst : ∀ t u : A.fibre a,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val) :
    ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.measuredGoodRow A P W ∧
      {z | Sum.elim a z ∈ (T.transition A).graph}=
        (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  obtain ⟨T,ha,hR⟩ := exists_promoted_prepared_centripetal_program h00 hc linear hκ hs hv
    A P a hsmall hΓ h hARV hPA hPrepared
  exact ⟨T,⟨ha,(gammaTransitionConstantParameterLocus_iff_row a _ _ f ω hR hW).mpr hConst⟩,hR⟩

end DiamondIntegral.Section6
