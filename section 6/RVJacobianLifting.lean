import «section 6».EverywhereMeasuredRVLifting
import «section 6».StructuralRVMeasures
import «section 6».ProperMeasuredRVLifts

/-! Every-degree measured and unmeasured RV Jacobian lifting over the
original VF-generated field base. Full total derivatives and the exact
Gamma identity hold everywhere, with fibre continuity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n : ℕ}

theorem lemma_6_31_measured_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V) :
    ∃ f : Map (rvLift U.object) (rvLift V.object),Function.Bijective f ∧
      (∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
      ∀ p,∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨F⟩ := exists_everywhere_measured_rv_lift_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hnt e
  exact ⟨F.map,F.bijective,F.labels,continuousOnGraphFibres_of_mixedDerivatives hv F.map
    (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩),F.measure⟩

theorem lemma_6_31_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : RVObject (M := M) (S : Set M) n} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u,∀ i,(U.value u i).val ≠ iRVZero) (hV : ∀ v,∀ i,(V.value v i).val ≠ iRVZero) :
    ∃ f : Map (rvLift U) (rvLift V),Function.Bijective f ∧
      (∀ p,e.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
      ∀ p,∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (rvGammaJacobian (U.value (liftLabelMap U p)) (V.value (e.hom.map (liftLabelMap U p)))
          (hU (liftLabelMap U p)) (hV (e.hom.map (liftLabelMap U p)))).val := by
  let e₀ := structuralMeasuredRVIso hc e hUF hVF hU hV
  obtain ⟨f,hf,hLabel,hCont,hMeasure⟩ := lemma_6_31_measured_vfGenerated
    h00 hc hκ hs hv S B hsmall hΓ hnt e₀
  refine ⟨f,hf,hLabel,hCont,fun p => ?_⟩
  obtain ⟨L,hL,hJ⟩ := hMeasure p
  refine ⟨L,hL,?_⟩
  have ht := liftLabelMap_target_of_graph e.hom.map f hLabel p
  change vfValue (LinearMap.toMatrix' L).det =
    (gammaMapValue (structuralMeasuredRVSource hc e hUF hU).form (liftLabelMap U p) /
      gammaMapValue (structuralMeasuredRVTarget hc V hVF hV).form (liftLabelMap V (f p))).val at hJ
  rw [ht] at hJ
  exact hJ.trans (congrArg (fun γ : Gamma M => γ.val) (e₀.gamma_jacobian (liftLabelMap U p)))

theorem exists_proper_measured_rv_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ f : Map (rvLift U.object) (rvLift V.object),ProperCovariantHomeomorphism f ∧
      (∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p,∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨F⟩ := exists_everywhere_measured_rv_lift_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hnt e
  exact ⟨F.map,properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ e hU hV
    F.map F.bijective F.labels (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩),F.labels,F.measure⟩

end DiamondIntegral.Section6
