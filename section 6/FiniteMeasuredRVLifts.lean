import «section 6».DiagonalRVLiftCalculus

/-! Everywhere measured lifting for finite original-label RV objects in
every degree. It constructs actual diagonal lifts and their full total
derivatives, rather than taking a local lifting statement as input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvTupleCenter_nonzero (U : MeasuredRVObject (M := M) S n)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.object.value u)
    (u : U.object.domain) (i : Fin n) : (a u).val i ≠ 0 := by
  intro hz
  apply U.nonzero u i
  have h := congrArg Subtype.val (congrFun (ha u) i)
  change (rv M ((a u).val i)).val = (U.object.value u i).val at h
  rw [hz,rv_zero] at h
  exact h.symm

theorem rvTupleCenter_volume_gamma_value (U : MeasuredRVObject (M := M) S n)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.object.value u)
    (u : U.object.domain) : (U.volumeGamma u).val = vfValue (∏ i, (a u).val i) := by
  let p : rvLift U.object := ⟨((a u).val,u.val),u,rfl,(ha u).symm⟩
  have hu : liftLabelMap U.object p = u := Subtype.ext rfl
  have h := rvLift_volume_gamma_value U p
  rw [hu] at h
  exact h

theorem diagonalRVLift_measure {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (b : Map V.object.domain (DefSet.univ (rawVFSpace (M := M) n) S))
    (ha : ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.object.value u)
    (hb : ∀ v, SpecialTransformations.Section4.tupleRV (b v).val = V.object.value v)
    (p : rvLift U.object) :
    ∃ L, HasMixedVFDerivativeAt (diagonalRVLift e.iso a b ha hb (rvTupleCenter_nonzero U a ha)) p L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object
            (diagonalRVLift e.iso a b ha hb (rvTupleCenter_nonzero U a ha) p))).val := by
  refine ⟨_,diagonalRVLift_derivative e.iso a b ha hb (rvTupleCenter_nonzero U a ha) p,?_⟩
  rw [det_vfDiagonalLinear,diagonalRVLift_label,Finset.prod_div_distrib]
  let u := liftLabelMap U.object p
  have h := congrArg (fun z : Gamma M => z.val) (e.gamma_jacobian u)
  change (gammaMapValue U.form u / gammaMapValue V.form (e.iso.hom.map u)).val =
    (V.volumeGamma (e.iso.hom.map u) / U.volumeGamma u).val at h
  simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv] at h
  have haV := rvTupleCenter_volume_gamma_value U a ha u
  have hbV := rvTupleCenter_volume_gamma_value V b hb (e.iso.hom.map u)
  change Values.vfValueHom ((∏ i, (b (e.iso.hom.map u)).val i) / (∏ i, (a u).val i)) = _
  rw [map_div₀]
  change vfValue (∏ i, (b (e.iso.hom.map u)).val i) / vfValue (∏ i, (a u).val i) = _
  rw [← haV,← hbV]
  simpa only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv] using h.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_measured_rv_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (hFin : U.object.domain.carrier.Finite) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
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
  let f := diagonalRVLift e.iso a b ha hb (rvTupleCenter_nonzero U a ha)
  have hm := diagonalRVLift_measure e a b ha hb
  exact ⟨f,diagonalRVLift_bijective e.iso a b ha hb (rvTupleCenter_nonzero U a ha) (rvTupleCenter_nonzero V b hb),
    fun p => ⟨liftLabelMap U.object p,rfl,rfl⟩,
    continuousOnGraphFibres_of_mixedDerivatives hv f (fun p => ⟨(hm p).choose,(hm p).choose_spec.1⟩),hm⟩

end DiamondIntegral.Section6
