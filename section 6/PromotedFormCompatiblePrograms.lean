import «section 6».FormCompatibleProgramLoci

/-! Actual form-compatible synchronized chains promote to whole
original-base programs with the core condition checked at every stage.
Intermediate full Gamma graphs are identified using exact transport. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_form_compatible_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {A₀ : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B₀ : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map A₀ B₀}
    {P₀ : Fin k → DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {ω : Map A₀ (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a))}
    (h : FormCompatibleSynchronizedChain (G := G) (Fin k) A₀ B₀ f P₀ ω) :
    ∀ (A : MixedSetParameterTemplate (M := M) S p n r)
      (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
      (W : GammaFormParameterTemplate (M := M) S p n r),
      A.fibre a=A₀ → (∀ i,(P i).fibre a=P₀ i) → IsRVPullback A₀.carrier →
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph →
      ∃ T : CentripetalProgramTemplate (M := M) S p n r s,
        a ∈ T.good A P ∧ a ∈ T.coreFormGood A W ∧
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
    change a ∈ gammaCoreConstantParameterLocus (focusComponentTransition T A) W.graph T.coordinate _
    rw [hj]
    exact (gammaCoreConstantParameterLocus_at_component a _ _ D h00 ω hGraph hW).mpr hForm
  | @comp r s t A₀ B₀ C₀ f g P₀ hPA ω hf η hTransport hg ihf ihg =>
    intro A P W hA hPeq hARV hW
    cases hA
    have hPF : (fun i => (P i).fibre a)=P₀ := funext hPeq
    subst P₀
    obtain ⟨F,hF,hFCore,hFGraph⟩ := ihf A P W rfl (fun _ => rfl) hARV hW
    have hfBij := hf.toSynchronized.toChain.toSpecial.bijective h00
    have hTarget : (F.target A).fibre a=B₀ :=
      (mixedRelationImageTemplate_at_image A (F.transition A).graph (F.transition A).definable a f hFGraph).trans
        (map_image_eq_target_of_surjective f hfBij.surjective)
    have hPieces (i) : (F.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
      mixedRelationImageTemplate_at_restriction (P i) (F.transition A).graph (F.transition A).definable a f (hPA i) hFGraph
    have hImage := gammaTransitionImage_at a (F.transition A).graph W.graph f hfBij ω hFGraph hW
    have hEta := exact_gamma_transport_eq_inverse f hfBij ω η hTransport
    have hFormGraph : {z | Sum.elim a z ∈ (W.transport (F.transition A)).graph}=
        (rawMixedSpace n s).relation rawGammaPresentation η.graph := by
      exact hImage.trans (congrArg (fun θ : Map B₀ (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)) =>
        (rawMixedSpace n s).relation rawGammaPresentation θ.graph) hEta).symm
    obtain ⟨H,hH,hHCore,hHGraph⟩ := ihg (F.target A) (fun i => F.pieceTarget A (P i))
      (W.transport (F.transition A)) hTarget hPieces (hf.toSynchronized.toChain.target_rvPullback h00 hARV) hFormGraph
    exact ⟨.comp F H,⟨hF,hH⟩,⟨hFCore,hHCore⟩,parameterRelationComp_at (P := rawMixedSpace n r)
      (Q := rawMixedSpace n s) (R := rawMixedSpace n t) (S := S) a (F.transition A).graph
      (H.transition (F.target A)).graph f g hFGraph hHGraph⟩

end DiamondIntegral.Section6
