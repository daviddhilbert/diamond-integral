import «section 6».FiniteMeasuredRVLifts

/-! Original VF-generated field-base adapters for finite-label measured
RV lifting in every degree, including proper covariant homeomorphisms
for doubly bounded source and target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_measured_rv_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨hW,hWS,hSW,hnt'⟩ := vfGenerated_base_support S B hnt
  exact exists_finite_measured_rv_lift hc h00 hs hv (vfFieldNames B.field) hW hWS hSW hnt' hsmall e hFin

theorem exists_finite_proper_measured_rv_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hU : U.doublyBounded) (hV : V.doublyBounded) (hFin : U.object.domain.carrier.Finite) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), ProperCovariantHomeomorphism f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨f,hf,hlab,hcont,hm⟩ := exists_finite_measured_rv_lift_vfGenerated h00 hc hs hv S B hsmall hnt e hFin
  exact ⟨f,properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ e hU hV f hf hlab
    (fun p => ⟨(hm p).choose,(hm p).choose_spec.1⟩),hlab,hm⟩

end DiamondIntegral.Section6
