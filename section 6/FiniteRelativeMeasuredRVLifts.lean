import «section 6».RelativeDiagonalCenters

/-! Actual everywhere differentiable relatively unary measured lifts of
finite-label relatively unary RV maps in every positive degree. -/

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

theorem exists_finite_relative_measured_rv_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (hFin : U.object.domain.carrier.Finite)
    (i : Fin n) (hUnary : RVUnaryRelativeAt e.iso.hom.map i) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      VFUnaryRelativeAt f i ∧ (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ContinuousOnGraphFibres f ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  have hVFin : V.object.domain.carrier.Finite := by
    letI : Finite U.object.domain := hFin.to_subtype
    apply (Set.finite_range (fun u : U.object.domain => (e.iso.hom.map u).val)).subset
    intro v hv
    exact ⟨e.iso.inv.map ⟨v,hv⟩,congrArg Subtype.val (SpecialTransformations.Section7.rvIso_apply_inv e.iso ⟨v,hv⟩)⟩
  obtain ⟨a,ha⟩ := exists_finite_rv_object_tuple_centers hc h00 hs hv W hW hWS hSW hnt hsmall U.object hFin
  obtain ⟨b,hb⟩ := exists_finite_rv_object_tuple_centers hc h00 hs hv W hW hWS hSW hnt hsmall V.object hVFin
  let b' := relativeTargetCenters e.iso a b i
  have hb' := relativeTargetCenters_rv e.iso a b i ha hb hUnary
  let f := diagonalRVLift e.iso a b' ha hb' (rvTupleCenter_nonzero U a ha)
  have hm := diagonalRVLift_measure e a b' ha hb'
  exact ⟨f,diagonalRVLift_bijective e.iso a b' ha hb' (rvTupleCenter_nonzero U a ha) (rvTupleCenter_nonzero V b' hb'),
    relative_diagonalRVLift_unary e.iso a b i ha hb hUnary (rvTupleCenter_nonzero U a ha),
    fun p => ⟨liftLabelMap U.object p,rfl,rfl⟩,
    continuousOnGraphFibres_of_mixedDerivatives hv f (fun p => ⟨(hm p).choose,(hm p).choose_spec.1⟩),hm⟩

end DiamondIntegral.Section6
