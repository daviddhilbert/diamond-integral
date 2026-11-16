import «section 6».FiniteMeasuredCentripetalPrograms

/-! A measured-admissible finite program realizes its actual
transported Gamma form, with exact equality everywhere and constancy on
its full output RV-label fibres. Its chain and every restriction remain
those of the original program realization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramRealization.transported_gamma_form
    (h00 : M ⊨ Axioms.ACVF00)
    {T : CentripetalProgramTemplate (M := M) S p n r s}
    {A : MixedSetParameterTemplate (M := M) S p n r}
    {P : Fin k → MixedSetParameterTemplate (M := M) S p n r} {a : Fin p → M}
    (F : CentripetalProgramRealization (G := G) T A P a)
    (W : GammaFormParameterTemplate (M := M) S p n r) (ha : a ∈ T.measuredGood A P W)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    ∃ η : Map ((T.target A).fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)),
      (∀ t : A.fibre a,(η (F.map t)).val=(ω t).val) ∧
      ∀ x y : (T.target A).fibre a,x.val.2=y.val.2 → (η x).val=(η y).val := by
  have hBij := F.chain.toChain.toSpecial.bijective h00
  let η := ω.comp (F.map.inverse hBij)
  have hConst := (gammaTransitionConstantParameterLocus_iff a _ _ F.map ω F.graph hW).mp ha.2
  refine ⟨η,?_,?_⟩
  · intro t
    change (ω (F.map.inverse hBij (F.map t))).val=(ω t).val
    rw [Map.inverse_apply]
  · intro x y hxy
    apply hConst (F.map.inverse hBij x) (F.map.inverse hBij y)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hxy

theorem CentripetalProgramTemplate.exists_measured_realization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.measuredGood A P W) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    ∃ F : CentripetalProgramRealization (G := G) T A P a,
      ∃ η : Map ((T.target A).fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)),
        (∀ t : A.fibre a,(η (F.map t)).val=(ω t).val) ∧
        ∀ x y : (T.target A).fibre a,x.val.2=y.val.2 → (η x).val=(η y).val := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha.1.1 hA hAD hPA hP
  obtain ⟨η,hη,hConst⟩ := F.transported_gamma_form h00 W ha ω hW
  exact ⟨F,η,hη,hConst⟩

end DiamondIntegral.Section6
