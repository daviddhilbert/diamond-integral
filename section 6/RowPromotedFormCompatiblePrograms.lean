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
import «section 6».RowFormCompatibleProgramLoci

/-! (Row-form version for Remark 6.20, translated from `PromotedFormCompatiblePrograms`.)
 Actual form-compatible synchronized chains promote to whole
original-base programs with the core condition checked at every stage.
Intermediate full Gamma graphs are identified using exact transportRow. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_form_compatible_program_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {A₀ : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B₀ : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map A₀ B₀}
    {P₀ : Fin k → DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {ω : RowFormOn A₀ qR}
    (h : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A₀ B₀ f P₀ ω) :
    ∀ (A : MixedSetParameterTemplate (M := M) S p n r)
      (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
      (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r),
      A.fibre a=A₀ → (∀ i,(P i).fibre a=P₀ i) → IsRVPullback A₀.carrier →
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph →
      ∃ T : CentripetalProgramTemplate (M := M) S p n r s,
        a ∈ T.good A P ∧ a ∈ T.coreFormGoodRow A W ∧
        {z | Sum.elim a z ∈ (T.transition A).graph}=
          (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  induction h with
  | identity A₀ hA₀ P₀ hPA hP ω =>
    intro A P W hA hPeq hARV hW
    cases hA
    exact ⟨.identity _,Set.mem_univ _,Set.mem_univ _,identityParameterTransition_at A a⟩
  | regularize A₀ hA₀ hAD P₀ hPA hP hPD ω =>
    intro A P W hA hPeq hARV hW
    cases hA
    exact ⟨.regularize _,Set.mem_univ _,Set.mem_univ _,regularizationParameterTransition_at A a⟩
  | @centripetal r A₀ D P₀ hPA E hData ω hForm =>
    intro A P W hA hPeq hARV hW
    cases hA
    have hPF : (fun i => (P i).fibre a)=P₀ := funext hPeq
    subst P₀
    obtain ⟨T,ha,hj,hU,hC,hF⟩ := exists_promoted_focus_component_template h00 hc linear hκ hs hv
      A P a hsmall hΓ D hARV E hData
    have hGraph : {z | Sum.elim a z ∈ focusComponentTransition T A}=
        (rawMixedSpace n r).relation (rawMixedSpace n (1+r)) D.bijection.graph := by
      apply focusComponentTransition_at T A a ha.1.1.1 ha.1.1.2 D hj.symm hU.symm hC.symm
      intro q
      have hu : q.val.2 ∈ D.activeTags.carrier := by simpa only [hU] using q.property.2
      rw [hF,totalFocusFibre_at D.focusMap q.val.2 q.val.1 ⟨q.property.1,hu⟩]
      exact (D.extendedFocus_active q.property.1 hu).trans (D.focusMap_eq ⟨q.val,q.property.1,hu⟩).symm
    refine ⟨.centripetal T,ha,?_,hGraph⟩
    change a ∈ gammaCoreConstantParameterLocusRow (focusComponentTransition T A) W.graph T.coordinate _
    rw [hj]
    exact (gammaCoreConstantParameterLocus_at_component_row a _ _ D h00 ω hGraph hW).mpr hForm
  | @comp r s t A₀ B₀ C₀ f g P₀ hPA ω hf η hTransport hg ihf ihg =>
    intro A P W hA hPeq hARV hW
    cases hA
    have hPF : (fun i => (P i).fibre a)=P₀ := funext hPeq
    subst P₀
    obtain ⟨F,hF,hFCore,hFGraph⟩ := ihf A P W rfl (fun _ => rfl) hARV hW
    have hfBij := hf.toSynchronizedRow.toChain.toSpecial.bijective h00
    have hTarget : (F.target A).fibre a=B₀ :=
      (mixedRelationImageTemplate_at_image A (F.transition A).graph (F.transition A).definable a f hFGraph).trans
        (map_image_eq_target_of_surjective f hfBij.surjective)
    have hPieces (i) : (F.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
      mixedRelationImageTemplate_at_restriction (P i) (F.transition A).graph (F.transition A).definable a f (hPA i) hFGraph
    have hImage := gammaTransitionImage_at_row a (F.transition A).graph W.graph f hfBij ω hFGraph hW
    have hEta := exact_gamma_transport_eq_inverse_row f hfBij ω η hTransport
    have hFormGraph : {z | Sum.elim a z ∈ (W.transportRow (F.transition A)).graph}=
        (rawMixedSpace n s).relation (rawRVSpace (M := M) qR) η.graph := by
      exact hImage.trans (congrArg (fun θ : RowFormOn B₀ qR =>
        (rawMixedSpace n s).relation (rawRVSpace (M := M) qR) θ.graph) hEta).symm
    obtain ⟨H,hH,hHCore,hHGraph⟩ := ihg (F.target A) (fun i => F.pieceTarget A (P i))
      (W.transportRow (F.transition A)) hTarget hPieces (hf.toSynchronizedRow.toChain.target_rvPullback h00 hARV) hFormGraph
    exact ⟨.comp F H,⟨hF,hH⟩,⟨hFCore,hHCore⟩,parameterRelationComp_at (P := rawMixedSpace n r)
      (Q := rawMixedSpace n s) (R := rawMixedSpace n t) (S := S) a (F.transition A).graph
      (H.transition (F.target A)).graph f g hFGraph hHGraph⟩

end DiamondIntegral.Section6
