import «section 6».CenteredPolydiscCharts
import «section 6».DiscVolumeComparison

/-! Constant-Jacobian-value volume descent for actual centered open
polydiscs with named chart coefficients. This uses the checked Gauss
graph construction and actual affine maps, not a volume comparison input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n r s : ℕ} {S : Set M}

theorem centered_polydisc_descent_named_charts [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (a b d e : Fin n → VF M) (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0)
    (hA : ∀ x : Fin n → VF M, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i-a i) < v (d i))
    (hB : ∀ x : Fin n → VF M, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i-b i) < v (e i))
    (dName : ∀ i, ((d i)⁻¹).val ∈ S) (eName : ∀ i, ((e i)⁻¹).val ∈ S)
    (aName : ∀ i, (-(d i)⁻¹*a i).val ∈ S) (bName : ∀ i, (-(e i)⁻¹*b i).val ∈ S)
    (c : VF M) (hc0 : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c) :
    v c = (∏ i, v (e i)) / ∏ i, v (d i) := by
  let u := affineMixedImage A (fun i => (d i)⁻¹) (fun i => -(d i)⁻¹*a i) dName aName
  let w := affineMixedImage B (fun i => (e i)⁻¹) (fun i => -(e i)⁻¹*b i) eName bName
  have hu := affineMixedImage_bijective A _ _ dName aName (fun i => inv_ne_zero (hd i))
  have hw := affineMixedImage_bijective B _ _ eName bName (fun i => inv_ne_zero (he i))
  let u' := u.inverse hu
  let F := w.comp (f.comp u')
  have hu' : Function.Bijective u' := (Equiv.ofBijective u hu).symm.bijective
  have hF : Function.Bijective F := hw.comp (hf.comp hu')
  let c' := ((∏ i, (e i)⁻¹)*c)*∏ i, d i
  have hc' : c' ≠ 0 := mul_ne_zero
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (he i))) hc0)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  letI : Valued (VF M) G := Valued.mk' v
  have hconstant (p : (affineMixedMap A _ _ dName aName).image)
      (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      ∃ J, HasMixedVFJacobianAt F p J ∧ v J = v c' := by
    have hp' := independent_map_of_finiteFibres hc u' (Map.finiteFibres_of_injective hu'.injective) p hp
    have hfp := independent_map_of_finiteFibres hc f (Map.finiteFibres_of_injective hf.injective) (u' p) hp'
    obtain ⟨L,hL⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv f (u' p) hp'
    obtain ⟨J,hJ,hval⟩ := hconst (u' p) hp'
    have huDer := hasMixedVFDerivativeAt_of_affine_formula hc hκ.le hs hsmall hv u' p hp d a
      (fun q => congrArg Prod.fst (centered_polydisc_chart_inverse A a d dName aName hd q))
    have hwDer := hasMixedVFDerivativeAt_of_affine_formula hc hκ.le hs hsmall hv w (f (u' p)) hfp
      (fun i => (e i)⁻¹) (fun i => -(e i)⁻¹*b i)
      (fun q => congrArg Prod.fst (affineMixedMap_apply B _ _ eName bName q))
    obtain ⟨K,hK⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv (f.comp u') p hp
    obtain ⟨_,hfdet,hfirst⟩ := mixedVFJacobian_comp_of_full_derivative huDer hL
    obtain ⟨hKdet,_,hlast⟩ := mixedVFJacobian_comp_of_full_derivative hK hwDer
    have h1 := hKdet.unique hfirst
    have h2 := hfdet.unique hJ
    refine ⟨_,hlast,?_⟩
    simp only [h1,h2,det_vfDiagonalLinear,c',map_mul,hval,mul_assoc]
  let F' := F.inverse hF
  have h := normalizedGammaDescent_of_reference_input hc hκ hs h00 hsmall v hv F F'
    (Map.inverse_apply F hF) (Map.apply_inverse F hF)
    (centered_polydisc_chart_projection v a d hd hA dName aName)
    (centered_polydisc_chart_projection v b e he hB eName bName) c' hc' hconstant
    IntegrationInACVF.Section2.ConstructedGaussGraph.acvf_graph_input
  have hne (z : Fin n → VF M) (hz : ∀ i, z i ≠ 0) : (∏ i, v (z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => v.ne_zero_iff.mpr (hz i))
  change v (((∏ i, (e i)⁻¹)*c)*∏ i, d i) = 1 at h
  rw [Finset.prod_inv_distrib,map_mul,map_mul,map_inv₀,map_prod,map_prod] at h
  apply (eq_div_iff (hne d hd)).mpr
  have hmul : (∏ i, v (e i))⁻¹*(v c*∏ i, v (d i)) = 1 := by rwa [← mul_assoc]
  simpa only [mul_one] using (inv_mul_eq_iff_eq_mul₀ (hne e he)).mp hmul

end DiamondIntegral.Section6
