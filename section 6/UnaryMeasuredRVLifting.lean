import «section 6».UnaryMeasuredLiftRepair
import «section 6».MixedDerivativeContinuity

/-! The everywhere unary measured RV lifting theorem over the actual
VF-generated field base. It uses the already proved generic lift and
repairs its finite old-label exceptional family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_unary_measured_rv_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (S : Set M) 1} (e : MeasuredRVIso U V) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ContinuousOnGraphFibres f ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨f,hf,hlab,E,hE,hDim,hGood⟩ :=
    exists_measured_rv_lift_ae_vfGenerated h00 hc hκ hs hv S B hsmall (by decide) e
  obtain ⟨hW,hWS,hSW,hnt'⟩ := vfGenerated_base_support S B hnt
  obtain ⟨F,hF,hFlab,hFm⟩ := exists_repaired_unary_measured_lift hc h00 hs hv
    (vfFieldNames B.field) hW hWS hSW hnt' hsmall e f hf hlab E hE hDim hGood
  exact ⟨F,hF,hFlab,continuousOnGraphFibres_of_mixedDerivatives hv F
    (fun p => ⟨(hFm p).choose,(hFm p).choose_spec.1⟩),hFm⟩

end DiamondIntegral.Section6
