import «section 6».FormCompatibleProgramRealizations
import «section 6».MeasuredFormCompatibleTargets

/-! Form-compatible actual programs produce full positive-degree
measured preparation witnesses, with the entire form-compatible permitted
chain and every literal protected image. Only one final regularization
is added to the specified program. -/

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

theorem CentripetalProgramTemplate.exists_form_compatible_measured_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p (n+1) r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p (n+1) r)
    (W : GammaFormParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M)
    (ha : a ∈ T.measuredFormGood A P W) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier) (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace (n+1) r).relation rawGammaPresentation ω.graph) :
    ∃ U : MeasuredCoordinatePreparation (G := G) (A.fibre a) (fun i => (P i).fibre a) hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) (A.fibre a) U.target U.map (fun i => (P i).fibre a) ω := by
  obtain ⟨F,hPhi⟩ := T.exists_form_compatible_realization h00 hc hκ hs hv A P W a ha.1.1.1 ha.2 hA hAD hPA hP ω hW
  let R : PreparedSynchronizedFamily (G := G) (A.fibre a) (fun i => (P i).fibre a) hPA := {
    arity := s
    target := (T.target A).fibre a
    map := F.map
    chain := F.chain
    proper := F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    doublyBounded := F.chain.toChain.toSpecial.target_vfDoublyBounded hAD
    pullback := F.chain.toChain.target_rvPullback h00 hARV
    prepared := (F.prepared_iff ha.1.1.1 hPA).mp ha.1.1 }
  exact R.measured_form_compatible_target h00 hc hκ hs hv ω hPhi
    ((gammaTransitionConstantParameterLocus_iff a _ _ F.map ω F.graph hW).mp ha.1.2)

end DiamondIntegral.Section6
