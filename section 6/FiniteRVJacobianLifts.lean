import «section 6».StructuralRVMeasures
import «section 6».FiniteMeasuredRVLiftFieldBase
import «section 6».ZeroArityRVIsomorphismLifts

/-! Everywhere unmeasured RV Jacobian lifting for finite original-label
objects in every degree, with actual definable graphs over the original
VF-generated field base. -/

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

theorem exists_finite_rv_jacobian_lift_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : RVObject (M := M) (S : Set M) n} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v, ∀ i, (V.value v i).val ≠ iRVZero) (hFin : U.domain.carrier.Finite) :
    ∃ f : Map (rvLift U) (rvLift V), Function.Bijective f ∧
      (∀ p, e.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (rvGammaJacobian (U.value (liftLabelMap U p)) (V.value (e.hom.map (liftLabelMap U p)))
          (hU (liftLabelMap U p)) (hV (e.hom.map (liftLabelMap U p)))).val := by
  let e₀ := structuralMeasuredRVIso hc e hUF hVF hU hV
  obtain ⟨f,hf,hlab,hcont,hm⟩ := exists_finite_measured_rv_lift_vfGenerated h00 hc hs hv S B hsmall hnt e₀ hFin
  refine ⟨f,hf,hlab,hcont,fun p => ?_⟩
  obtain ⟨L,hL,hJ⟩ := hm p
  refine ⟨L,hL,?_⟩
  have ht := liftLabelMap_target_of_graph e.hom.map f hlab p
  change vfValue (LinearMap.toMatrix' L).det =
    (gammaMapValue (structuralMeasuredRVSource hc e hUF hU).form (liftLabelMap U p) /
      gammaMapValue (structuralMeasuredRVTarget hc V hVF hV).form (liftLabelMap V (f p))).val at hJ
  rw [ht] at hJ
  exact hJ.trans (congrArg (fun z : Gamma M => z.val) (e₀.gamma_jacobian (liftLabelMap U p)))

theorem lemma_6_31_unmeasured_zero_arity
    {S : Set M} {U V : RVObject (M := M) S 0} (e : U ≅ V)
    (hU : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v, ∀ i, (V.value v i).val ≠ iRVZero) :
    ∃ f : Map (rvLift U) (rvLift V), Function.Bijective f ∧
      (∀ p, e.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (rvGammaJacobian (U.value (liftLabelMap U p)) (V.value (e.hom.map (liftLabelMap U p)))
          (hU (liftLabelMap U p)) (hV (e.hom.map (liftLabelMap U p)))).val := by
  refine ⟨zeroArityRVLift e,zeroArityRVLift_bijective e,
    fun p => ⟨liftLabelMap U p,rfl,rfl⟩,fun p => ⟨_,mixedDerivative_zero_arity _ p,?_⟩⟩
  rw [LinearMap.toMatrix'_id,Matrix.det_one]
  simp only [rvGammaJacobian,rvVolumeGamma,Finset.univ_eq_empty,Finset.prod_empty,div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one,map_one]

end DiamondIntegral.Section6
