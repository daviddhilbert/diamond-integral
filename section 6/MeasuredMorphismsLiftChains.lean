import «section 6».MeasuredVFChainLifting

/-! Lemma 6.33 in every positive degree and arbitrary RV dimension.
Actual relatively unary measured VF components have full total
derivatives everywhere. Doubly bounded objects give proper covariant
homeomorphisms for every component and the full composite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n : ℕ}

theorem lemma_6_33_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) n U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) :=
  exists_measured_vf_unary_chain_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hnt hn e

theorem lemma_6_33_doublyBounded_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) n U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      T.doublyBounded ∧ T.properComponents ∧ ProperCovariantHomeomorphism T.lift.map := by
  obtain ⟨T,hT,hTB⟩ := lemma_6_33_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hnt hn e
  have hBounds := hTB ⟨hU,hV⟩
  exact ⟨T,hT,hBounds,T.properComponents_of_doublyBounded h00 hc linear hκ hs hv hsmall hΓ hBounds,
    properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ T.iso hU hV
      T.lift.map T.lift.bijective T.lift.labels
      (fun p => ⟨(T.lift.measure p).choose,(T.lift.measure p).choose_spec.1⟩)⟩

end DiamondIntegral.Section6
