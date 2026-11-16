import «section 6».UnaryAffineRVLiftDerivative

/-! Finite-label measured RV isomorphisms have everywhere differentiable
actual VF lifts. The Gamma Jacobian equation is derived from the two
center values and the given measured RV balance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem unaryCenter_nonzero (U : MeasuredRVObject (M := M) S 1)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.object.value u 0) (u : U.object.domain) :
    (a u).val 0 ≠ 0 := by
  intro hz
  apply U.nonzero u 0
  rw [← ha u,hz,rv_zero]
  rfl

theorem unaryCenter_volume_gamma_value (U : MeasuredRVObject (M := M) S 1)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.object.value u 0) (u : U.object.domain) :
    (U.volumeGamma u).val = vfValue ((a u).val 0) := by
  have hp : ((a u).val,u.val) ∈ (rvLift U.object).carrier := by
    refine ⟨u,rfl,?_⟩
    funext i
    fin_cases i
    exact (ha u).symm
  let p : rvLift U.object := ⟨((a u).val,u.val),hp⟩
  have hu : liftLabelMap U.object p = u := Subtype.ext rfl
  have h := rvLift_volume_gamma_value U p
  rw [hu] at h
  simpa only [Fin.prod_univ_one] using h

theorem unaryAffineRVLift_measure {U V : MeasuredRVObject (M := M) S 1} (e : MeasuredRVIso U V)
    (a : Map U.object.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (b : Map V.object.domain (DefSet.univ (rawVFSpace (M := M) 1) S))
    (ha : ∀ u, rv M ((a u).val 0) = U.object.value u 0)
    (hb : ∀ v, rv M ((b v).val 0) = V.object.value v 0) (p : rvLift U.object) :
    ∃ L, HasMixedVFDerivativeAt (unaryAffineRVLift e.iso a b ha hb (unaryCenter_nonzero U a ha)) p L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object
            (unaryAffineRVLift e.iso a b ha hb (unaryCenter_nonzero U a ha) p))).val := by
  refine ⟨_,unaryAffineRVLift_derivative e.iso a b ha hb (unaryCenter_nonzero U a ha) p,?_⟩
  rw [unaryAffineRVLift_determinant,unaryAffineRVLift_label]
  let u := liftLabelMap U.object p
  have h := congrArg (fun z : Gamma M => z.val) (e.gamma_jacobian u)
  change (gammaMapValue U.form u / gammaMapValue V.form (e.iso.hom.map u)).val =
    (V.volumeGamma (e.iso.hom.map u) / U.volumeGamma u).val at h
  simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv] at h
  have haV := unaryCenter_volume_gamma_value U a ha u
  have hbV := unaryCenter_volume_gamma_value V b hb (e.iso.hom.map u)
  change Values.vfValueHom ((b (e.iso.hom.map u)).val 0 / (a u).val 0) = _
  rw [map_div₀]
  change vfValue ((b (e.iso.hom.map u)).val 0) / vfValue ((a u).val 0) = _
  rw [← haV,← hbV]
  simpa only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv] using h.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_unary_measured_rv_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) {U V : MeasuredRVObject (M := M) S 1}
    (e : MeasuredRVIso U V) (hFin : U.object.domain.carrier.Finite) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det =
          (gammaMapValue U.form (liftLabelMap U.object p) /
            gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  have hVFin : V.object.domain.carrier.Finite := by
    letI : Finite U.object.domain := hFin.to_subtype
    apply (Set.finite_range (fun u : U.object.domain => (e.iso.hom.map u).val)).subset
    intro v hv
    exact ⟨e.iso.inv.map ⟨v,hv⟩,congrArg Subtype.val (SpecialTransformations.Section7.rvIso_apply_inv e.iso ⟨v,hv⟩)⟩
  obtain ⟨a,ha⟩ := exists_finite_unary_rv_object_centers hc h00 hs hv W hW hWS hSW hnt hsmall U.object hFin
  obtain ⟨b,hb⟩ := exists_finite_unary_rv_object_centers hc h00 hs hv W hW hWS hSW hnt hsmall V.object hVFin
  refine ⟨unaryAffineRVLift e.iso a b ha hb (unaryCenter_nonzero U a ha),
    unaryAffineRVLift_bijective e.iso a b ha hb (unaryCenter_nonzero U a ha) (unaryCenter_nonzero V b hb),
    fun p => ⟨liftLabelMap U.object p,rfl,rfl⟩,unaryAffineRVLift_measure e a b ha hb⟩

end DiamondIntegral.Section6
