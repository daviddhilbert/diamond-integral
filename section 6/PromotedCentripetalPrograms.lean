import «section 6».CentripetalProgramAdmissibility
import «section 6».PromotedFocusComponentTemplates

/-! Every actual finite synchronized chain on a pullback fibre is a
specialization of a whole original-base admissible program. Promotion
retains the exact composite graph, including all original RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_promoted_centripetal_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {A₀ : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B₀ : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map A₀ B₀}
    {P₀ : Fin k → DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (h : SynchronizedCentripetalChain (G := G) (Fin k) A₀ B₀ f P₀) :
    ∀ (A : MixedSetParameterTemplate (M := M) S p n r)
      (P : Fin k → MixedSetParameterTemplate (M := M) S p n r),
      A.fibre a=A₀ → (∀ i,(P i).fibre a=P₀ i) → IsRVPullback A₀.carrier →
      ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.good A P ∧
        {z | Sum.elim a z ∈ (T.transition A).graph}=
          (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  induction h with
  | identity A₀ hA₀ P₀ hPA hP =>
    intro A P hA hPeq hARV
    cases hA
    exact ⟨.identity _,Set.mem_univ _,identityParameterTransition_at A a⟩
  | regularize A₀ hA₀ hAD P₀ hPA hP hPD =>
    intro A P hA hPeq hARV
    cases hA
    exact ⟨.regularize _,Set.mem_univ _,regularizationParameterTransition_at A a⟩
  | centripetal A₀ D P₀ hPA E hData =>
    intro A P hA hPeq hARV
    cases hA
    have hPF : (fun i => (P i).fibre a)=P₀ := funext hPeq
    subst P₀
    obtain ⟨T,ha,hj,hU,hC,hF⟩ := exists_promoted_focus_component_template h00 hc linear hκ hs hv
      A P a hsmall hΓ D hARV E hData
    refine ⟨.centripetal T,ha,?_⟩
    apply focusComponentTransition_at T A a ha.1.1.1 ha.1.1.2 D hj.symm hU.symm hC.symm
    intro q
    have hu : q.val.2 ∈ D.activeTags.carrier := by simpa only [hU] using q.property.2
    rw [hF,totalFocusFibre_at D.focusMap q.val.2 q.val.1 ⟨q.property.1,hu⟩]
    exact (D.extendedFocus_active q.property.1 hu).trans (D.focusMap_eq ⟨q.val,q.property.1,hu⟩).symm
  | @comp r s t A₀ B₀ C₀ f g P₀ hPA hf hg ihf ihg =>
    intro A P hA hPeq hARV
    cases hA
    have hPF : (fun i => (P i).fibre a)=P₀ := funext hPeq
    subst P₀
    obtain ⟨F,hF,hFGraph⟩ := ihf A P rfl (fun _ => rfl) hARV
    have hTarget : (F.target A).fibre a=B₀ :=
      (mixedRelationImageTemplate_at_image A (F.transition A).graph (F.transition A).definable a f hFGraph).trans
        (map_image_eq_target_of_surjective f (hf.toChain.toSpecial.bijective h00).surjective)
    have hPieces (i) : (F.pieceTarget A (P i)).fibre a=(f.restrict (hPA i)).image :=
      mixedRelationImageTemplate_at_restriction (P i) (F.transition A).graph (F.transition A).definable a f (hPA i) hFGraph
    obtain ⟨H,hH,hHGraph⟩ := ihg (F.target A) (fun i => F.pieceTarget A (P i)) hTarget hPieces
      (hf.toChain.target_rvPullback h00 hARV)
    exact ⟨.comp F H,⟨hF,hH⟩,parameterRelationComp_at (P := rawMixedSpace n r)
      (Q := rawMixedSpace n s) (R := rawMixedSpace n t) (S := S) a (F.transition A).graph
      (H.transition (F.target A)).graph f g hFGraph hHGraph⟩

end DiamondIntegral.Section6
