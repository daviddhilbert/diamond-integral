import «section 6».FormCompatibleProgramLoci
import «section 6».FormCompatibleChainTransport

/-! The exact target computed by a finite program retains the actual
form-compatible common map and all literal protected image sets. -/

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

theorem CentripetalProgramRealization.ofMap_form_compatible
    (h00 : M ⊨ Axioms.ACVF00)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} (f : Map (A.fibre a) B)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hChain : FormCompatibleSynchronizedChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a) ω)
    (hGraph : {z | Sum.elim a z ∈ (T.transition A).graph}=
      (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph) :
    ∃ F : CentripetalProgramRealization (G := G) T A P a,
      FormCompatibleSynchronizedChain (G := G) (Fin k) (A.fibre a) ((T.target A).fibre a) F.map
        (fun i => (P i).fibre a) ω := by
  have hTarget : (T.target A).fibre a=B :=
    (mixedRelationImageTemplate_at_image A (T.transition A).graph (T.transition A).definable a f hGraph).trans
      (map_image_eq_target_of_surjective f (hChain.toSynchronized.toChain.toSpecial.bijective h00).surjective)
  let g := changeMapTarget f hTarget.symm
  have hGChain := hChain.changeTarget hTarget.symm (fun x => (changeMapTarget_value f hTarget.symm x).symm)
  have hGGraph : {z | Sum.elim a z ∈ (T.transition A).graph}=
      (rawMixedSpace n r).relation (rawMixedSpace n s) g.graph := by
    cases hTarget
    exact hGraph
  exact ⟨⟨g,hGChain.toSynchronized,hGGraph,fun i hPA =>
    mixedRelationImageTemplate_at_restriction (P i) (T.transition A).graph
      (T.transition A).definable a g hPA hGGraph⟩,hGChain⟩

end DiamondIntegral.Section6
