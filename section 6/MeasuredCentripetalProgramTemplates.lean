import «section 6».GammaTransitionSemantics

/-! Whole-program measured preparation has one original-base definable
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure GammaFormParameterTemplate (S : Set M) (p n r : ℕ) where
  graph : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)
  definable : S.Definable LRV graph

theorem exists_promoted_gamma_form_template (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a))) :
    ∃ W : GammaFormParameterTemplate (M := M) S p n r,
      {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a
    ((rawMixedSpace n r).relation rawGammaPresentation ω.graph) ω.graph_definable
  refine ⟨⟨{z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R},hR⟩,?_⟩
  ext z
  exact Set.ext_iff.mp hSection z

def CentripetalProgramTemplate.measuredGood
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : Set (Fin p → M) :=
  T.preparedGood A P ∩ gammaTransitionConstantParameterLocus (T.transition A).graph W.graph

theorem CentripetalProgramTemplate.measuredGood_definable
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : S.Definable LRV (T.measuredGood A P W) :=
  (T.preparedGood_definable A P).inter
    (gammaTransitionConstantParameterLocus_definable _ _ (T.transition A).definable W.definable)

theorem exists_promoted_measured_centripetal_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r)
    (a : Fin p → M) (hsmall : Cardinal.mk ↥(S ∪ Set.range a) < κ)
    (hΓ : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M))
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} {f : Map (A.fibre a) B}
    (h : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a))
    (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hPA i)).image.carrier)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hConst : ∀ t u : A.fibre a,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val) :
    ∃ T : CentripetalProgramTemplate (M := M) S p n r s,a ∈ T.measuredGood A P W ∧
      {z | Sum.elim a z ∈ (T.transition A).graph}=
        (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  obtain ⟨T,ha,hR⟩ := exists_promoted_prepared_centripetal_program h00 hc linear hκ hs hv
    A P a hsmall hΓ h hARV hPA hPrepared
  exact ⟨T,⟨ha,(gammaTransitionConstantParameterLocus_iff a _ _ f ω hR hW).mpr hConst⟩,hR⟩

end DiamondIntegral.Section6
