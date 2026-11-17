import «section 3».GammaMeasuredSemiringLift
import IntegrationSection2.GammaVolumeDescent
import IntegrationSection2.ConstructedGaussGraph

/-! Gamma-valued descent on every actual RV label, using only the
generic Gamma measure equation and the proved polydisc theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section2
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {k : ℕ}

theorem gammaGenericLift_pointwise_descent
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) {S : Set M} (hS : Cardinal.mk S < κ)
    {U V : SpecialTransformations.Section4.RVObject (M := M) S k} (e : U ≅ V)
    (hU : ∀ u : U.domain, ∀ i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v : V.domain, ∀ i, (V.value v i).val ≠ iRVZero)
    (ω : GammaVolumeForm hc U.domain) (π : GammaVolumeForm hc V.domain)
    (f : Map (rvLift U) (rvLift V)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2)
    (hmeasure : ∀ p : rvLift U, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : Section2.VF M, HasMixedVFJacobianAt f p J ∧
        (gammaFormValue ω (liftLabelMap U p)).val =
          (gammaFormValue π (liftLabelMap V (f p))).val * Values.vfValueHom J) :
    ∀ u : U.domain, gammaFormValue ω u = gammaFormValue π (e.hom.map u) *
      rvGammaJacobian (U.value u) (V.value (e.hom.map u)) (hU u) (hV (e.hom.map u)) := by
  intro u
  let rho := gammaFormValue ω u / gammaFormValue π (e.hom.map u)
  obtain ⟨c,hcrho⟩ := Section2.vfValue_surjective rho.val
  have hc0 : c ≠ 0 := by
    intro hz
    exact rho.property (hcrho.symm.trans ((Section2.vfValue_eq_infinity_iff c).mpr hz))
  obtain ⟨a,ha0,ha⟩ := LiftFibreGeometry.nonzero_representatives (U.value u) (hU u)
  obtain ⟨b,hb0,hb⟩ := LiftFibreGeometry.nonzero_representatives (V.value (e.hom.map u)) (hV (e.hom.map u))
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  let T := FixedLabelLift.labelBase e u
  let N := insert (-1 : Section2.VF M).val
    (Set.range (fun i => ((a i)⁻¹).val) ∪ Set.range (fun i => ((b i)⁻¹).val))
  let R := T ∪ N
  have hTR : T ⊆ R := Set.subset_union_left
  have hsmall : Cardinal.mk R < κ := small_union_finite hκ.le T
    (FixedLabelLift.small_base hκ.le hS e u) N
      (((Set.finite_range _).union (Set.finite_range _)).insert _)
  let f₀ := (FixedLabelLift.fibreMap e f hlabel u).extend hTR
  have hSR : S ⊆ R := (FixedLabelLift.base_subset e u).trans hTR
  have hconst (p : (FixedLabelLift.source e u).extend hTR)
      (hp : AlgebraicIndependent (vfParameterField R) p.val.1) :
      ∃ J : Section2.VF M, HasMixedVFJacobianAt f₀ p J ∧ v J = v c := by
    let q : rvLift U := ⟨p.val,((FixedLabelLift.source_mem e u p.val).mp p.property).1⟩
    have hfield : vfParameterField S ≤ vfParameterField R := by
      apply Subfield.closure_mono
      intro x hx
      exact hSR hx
    have hpS : AlgebraicIndependent (vfParameterField S) q.val.1 :=
      algebraicIndependent_of_subfield_le hfield q.val.1 hp
    obtain ⟨J,hJ,hm⟩ := hmeasure q hpS
    have hs : liftLabelMap U q = u := Subtype.ext ((FixedLabelLift.source_mem e u p.val).mp p.property).2
    have ht : liftLabelMap V (f q) = e.hom.map u := by
      apply Subtype.ext
      exact ((e.hom.map.graph_apply (liftLabelMap U q) (f q).val.2).mp (hlabel q)).symm.trans
        (congrArg Subtype.val (congrArg e.hom.map hs))
    rw [hs,ht] at hm
    have hπ : (gammaFormValue π (e.hom.map u)).val ≠ 0 := by
      rw [← Values.infinity_eq_zero]
      exact (gammaFormValue π (e.hom.map u)).property
    have hval : Values.vfValueHom J = rho.val := by
      change Values.vfValueHom J = (gammaFormValue ω u / gammaFormValue π (e.hom.map u)).val
      rw [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv,←div_eq_mul_inv]
      apply (eq_div_iff hπ).mpr
      exact (mul_comm _ _).trans hm.symm
    refine ⟨J,FixedLabelLift.jacobian e f hlabel u p hJ,?_⟩
    exact (Values.vf_value_eq_iff v hv J c).mp (hval.trans hcrho.symm)
  have hdesc := gammaDescent_polydiscs_of_reference_input hc hκ hs h00 hsmall v hv
    f₀ (FixedLabelLift.fibreMap_bijective e f hf hlabel u) a b ha0 hb0
    (LiftFibreGeometry.projection v hv U u ((FixedLabelLift.source_base_subset e u).trans hTR) a ha)
    (LiftFibreGeometry.projection v hv V (e.hom.map u) ((FixedLabelLift.target_base_subset e u).trans hTR) b hb)
    (fun i => Or.inr (Set.mem_insert_of_mem _ (Or.inl (Set.mem_range_self i))))
    (fun i => Or.inr (Set.mem_insert_of_mem _ (Or.inr (Set.mem_range_self i))))
    (Or.inr (Set.mem_insert _ _)) c hc0 hconst ConstructedGaussGraph.acvf_graph_input
  have hactual : Values.vfValueHom c = Values.vfValueHom ((∏ i,b i) / ∏ i,a i) := by
    apply (Values.vf_value_eq_iff v hv _ _).mpr
    simpa only [map_div₀,map_prod] using hdesc
  have hvolume (t : Fin k → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero)
      (x : Fin k → Section2.VF M) (hx : tupleRV x = t) :
      (rvVolumeGamma t ht).val = Values.vfValueHom (∏ i,x i) := by
    subst t
    rw [map_prod]
    exact map_prod Values.gammaValHom (fun i => Values.gammaOf (tupleRV x i) (ht i)) Finset.univ
  have hratio : rho = rvGammaJacobian (U.value u) (V.value (e.hom.map u)) (hU u) (hV (e.hom.map u)) := by
    apply Subtype.ext
    rw [rvGammaJacobian,div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv,←div_eq_mul_inv]
    rw [hvolume _ _ b hb,hvolume _ _ a ha,←map_div₀]
    exact hcrho.symm.trans hactual
  calc
    gammaFormValue ω u = gammaFormValue π (e.hom.map u) * rho := by
      dsimp only [rho]
      symm
      rw [div_eq_mul_inv]
      calc
        _ = (gammaFormValue π (e.hom.map u) * (gammaFormValue π (e.hom.map u))⁻¹) * gammaFormValue ω u := by ac_rfl
        _ = _ := by rw [mul_inv_cancel,one_mul]
    _ = _ := congrArg (fun z => gammaFormValue π (e.hom.map u) * z) hratio

end DiamondIntegral.Section3
