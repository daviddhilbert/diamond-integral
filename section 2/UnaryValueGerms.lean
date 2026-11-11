import «section 2».Conventions
import Section8.UnarySlope

/-! The fixed-centre valuation calculation used in 2.51. This applies
the checked polynomial-relation and unary-germ results from [17]; it does
not require the centre to belong to a generic differentiability locus. -/

set_option backward.isDefEq.respectTransparency false
open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VF M) Γ]

theorem strict_vf_ball_mem_nhds (a r : VF M) (hr : r ≠ 0) :
    {x : VF M | Valued.v (x-a) < Valued.v r} ∈ 𝓝 a :=
  ValuedPolydisc.side_mem_nhds
    (⟨fun _ => a,fun _ => r,fun _ => hr⟩ : ValuedPolydisc (Valued.v : Valuation (VF M) Γ) 1) 0

theorem exists_positive_gamma_power_germ
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VF M → VF M) (hf : S.Definable LRV (unaryScalarGraph f)) (a : VF M)
    (hclose : ∀ r s : VF M, r ≠ 0 → s ≠ 0 →
      ∃ x, x ≠ a ∧ Valued.v (x-a) < Valued.v r ∧ Valued.v (f x) < Valued.v s)
    (hnonzero : ∀ᶠ x in 𝓝 a, x ≠ a → f x ≠ 0) :
    ∃ (p q : ℕ) (c r : Gamma M), 0 < p ∧ 0 < q ∧ gammaPowerGerm f a p q c r := by
  classical
  obtain ⟨P,hP,hPzero⟩ := unary_graph_polynomial_relation hc hs hsmall f hf
  let E := vfParameterField S
  let Q := MvPolynomial.map E.subtype P
  have hQ : Q ≠ 0 := by
    intro h
    exact hP ((MvPolynomial.map_injective E.subtype Subtype.val_injective)
      (h.trans (map_zero _).symm))
  obtain ⟨D,c,hc₀,heval⟩ := mvPolynomial_has_shape Q hQ
  have hpoly (x : VF M) :
      ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval (f x) = 0 := by
    rw [← heval]
    change MvPolynomial.eval ![x,f x] (MvPolynomial.map E.subtype P) = 0
    rw [MvPolynomial.eval_map]
    exact hPzero x
  rcases scalar_eventually_zero_or_positive_power hc hv hf D c hc₀ hpoly a hclose with hzero | hpower
  · have hnear : {x : VF M | (x ≠ a → f x = 0) ∧ (x ≠ a → f x ≠ 0)} ∈ 𝓝 a :=
      hzero.and hnonzero
    have hinf := infinite_valued_neighbourhood (model_valuation_nontrivial hv) a hnear
    apply False.elim
    apply hinf ((Set.finite_singleton a).subset ?_)
    intro x hx
    by_contra hxa
    exact (hx.2 hxa) (hx.1 hxa)
  · obtain ⟨p,q,hp,hpbound,hq,hqbound,s,hs₀,h⟩ := hpower
    obtain ⟨c,r,hgerm⟩ := exists_gammaPowerGerm hv f a s hs₀ p q (Nat.ne_of_gt hq) h
    exact ⟨p,q,c,r,hp,hq,hgerm⟩

theorem exists_positive_gamma_power_germ_of_continuousAt
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VF M → VF M) (hf : S.Definable LRV (unaryScalarGraph f)) (a : VF M)
    (hcont : ContinuousAt f a) (hzero : f a = 0)
    (hnonzero : ∀ᶠ x in 𝓝 a, x ≠ a → f x ≠ 0) :
    ∃ (p q : ℕ) (c r : Gamma M), 0 < p ∧ 0 < q ∧ gammaPowerGerm f a p q c r := by
  apply exists_positive_gamma_power_germ hc hs hsmall hv f hf a ?_ hnonzero
  intro r s hr hs₀
  have hin := strict_vf_ball_mem_nhds (Γ := Γ) a r hr
  have hout : {x : VF M | Valued.v (f x) < Valued.v s} ∈ 𝓝 a := by
    have h := hcont.preimage_mem_nhds (strict_vf_ball_mem_nhds (Γ := Γ) (f a) s hs₀)
    simpa only [hzero,sub_zero,Set.preimage_ofPred_eq] using h
  have hnear : {x : VF M | Valued.v (x-a) < Valued.v r ∧ Valued.v (f x) < Valued.v s} ∈ 𝓝 a :=
    Filter.inter_mem hin hout
  have hinf := infinite_valued_neighbourhood (model_valuation_nontrivial hv) a hnear
  obtain ⟨x,hx,hxa⟩ := Set.not_subset.mp
    (show ¬ {x : VF M | Valued.v (x-a) < Valued.v r ∧ Valued.v (f x) < Valued.v s} ⊆ {a} from
      fun h => hinf ((Set.finite_singleton a).subset h))
  exact ⟨x,fun he => hxa (Set.mem_singleton_iff.mpr he),hx⟩

end DiamondIntegral.Section2
