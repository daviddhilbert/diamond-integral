import «section 6».RVIsomorphismLiftGraphFibres

/-! Every everywhere differentiable bijective lift of a doubly bounded
measured RV isomorphism is a proper covariant homeomorphism. The source
and range graph fibres and the original-base radius hypotheses are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properHomeomorphism_of_measuredRVIsoLift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f)
    (hlabel : ∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2)
    (hD : ∀ p, ∃ L, HasMixedVFDerivativeAt f p L) : ProperCovariantHomeomorphism f := by
  have hA := measuredRVLift_properInvariant h00 hc hκ hs hv U hU
  have hB := measuredRVLift_properInvariant h00 hc hκ hs hv V hV
  have hcont := continuousOnGraphFibres_of_mixedDerivatives hv f hD
  have hcov := properCovariant_of_clopen_ranges h00 hc hκ hs hv f hA hB hcont
    (graphFibreSource_isOpen_of_mixedDerivatives hv f hD)
    (measuredRVIsoLift_graphFibreRange_isClopen e hv f hf.surjective hlabel)
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ f hcov hf hcont

def VFUnaryRelativeAt {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (i : Fin n) : Prop := ∀ p : A, ∀ j : Fin n, j ≠ i → (f p).val.1 j = p.val.1 j

theorem vfUnaryRelativeAt_degree_one {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) : VFUnaryRelativeAt f 0 := by
  intro p j hj
  exact (hj (Subsingleton.elim _ _)).elim

theorem lemma_6_33_degree_one_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) 1} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), ProperCovariantHomeomorphism f ∧
      VFUnaryRelativeAt f 0 ∧ (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨f,hf,hlab,hcont,hm⟩ := exists_unary_measured_rv_lift_vfGenerated h00 hc hκ hs hv S B hsmall hnt e
  exact ⟨f,properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ e hU hV f hf hlab
    (fun p => ⟨(hm p).choose,(hm p).choose_spec.1⟩),vfUnaryRelativeAt_degree_one f,hlab,hm⟩

end DiamondIntegral.Section6
