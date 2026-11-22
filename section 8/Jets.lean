import «section 8».JetSeries
import Section8.UniformBalls

/-! The truncations of the nonarchimedean Milnor fiber are the jet varieties ((z:coeff:change), second
equality).

Let `f ∈ ℂ[x₁, …, x_d]` and `m ≥ 1`. In the concrete model, `𝒳_f = {x ∈ 𝔪^d | rv(f(x)) = rv(t)}`
(`rawMilnor f`) is definable over `ℂ((t))` and invariant for the cutoffs `β = (1, …, 1)` at level
`m` (`milnor_invariant_conc`).

* `IsJet f m a`: `a = (a_{i,k})_{i ≤ d, k ≤ m}` with `a_{i,0} = 0` and `f(Σ_k a_{i,k} s^k) ≡ s^m
  mod s^{m+1}`: the truncated arcs `φ ∈ 𝔸^d(ℂ[s]/(s^{m+1}))` with `φ(0) = 0` and `f(φ) = s^m mod
  s^{m+1}` of the manuscript's (f:m:arc), in the coordinates `a_{i,k}`.
* `milnor_coeffSet`: the coefficient set of the truncation `𝒳_f[m;β]` is the jet set.
* `milnor_trunc_eq`: `𝒳_f[m;β]` is the image of the jet set under
  `a ↦ (rv(a_{i,k} t^{k/m}))_{i,k}`: with `s = t^{1/m}`, the truncation is the jet variety, and the
  diagonal action of `μ_m` on `L_{k/m}` is `s ↦ ζ s` on the coefficient of `s^k`.
* `jetObject`: the jet set as a diagonal constructible object with weights `k/m`; it is the
  truncation object of `𝒳_f` (`jetObject_eq`), so its class is `Θ` of the class of `𝒳_f[m;β]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable DiamondIntegral.Section8.NormalForm

local instance jetStructure : LRV.Structure Carrier := canonicalInterpret
local instance jetModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {d : ℕ} (f : MvPolynomial (Fin d) ℂ)

/-! ### The concrete Milnor fiber -/

/-- `t` in the concrete model. -/
abbrev tS : Ser := puiseuxRoot 1

/-- The field-sort element of a series. -/
abbrev vfOf (g : Ser) : VFType (M := Carrier) := taggedFieldEquiv.symm g

/-- `f` with coefficients in the field sort of the concrete model. -/
def fC : MvPolynomial (Fin d) (VFType (M := Carrier)) :=
  MvPolynomial.map (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant) f

/-- The codes of a raw tuple, for the polynomial codes. -/
def codesOf (z : Fin (d + 0) → Carrier) : Fin d ⊕ Fin 0 → Carrier := Sum.elim z Fin.elim0

/-- `𝒳_f` as a set of raw tuples of the concrete model. -/
def rawMilnor : Set (Fin (d + 0) → Carrier) :=
  {z | (∀ i, z i ∈ SpecialTransformations.Section8.rawOpenBall (vfOf 0).val (vfOf 1).val) ∧
    iRv (SpecialTransformations.Section5.mvPolynomialCode (fC f) (codesOf z)) = iRv (vfOf tS).val}

theorem base_mem_of (g : Ser) (hg : g ∈ puiseuxBaseSubfield ℂ) : baseCarrier (vfOf g).val := hg

theorem const_mem_base (c : ℂ) : puiseuxConstant c ∈ puiseuxBaseSubfield ℂ :=
  (puiseuxBaseConstant c).property

theorem rawMilnor_definable : {c | baseCarrier c}.Definable LRV (rawMilnor f) := by
  have h0 : (vfOf 0).val ∈ {c : Carrier | baseCarrier c} := base_mem_of 0 (zero_mem _)
  have h1 : (vfOf 1).val ∈ {c : Carrier | baseCarrier c} := base_mem_of 1 (one_mem _)
  have ht : (vfOf tS).val ∈ {c : Carrier | baseCarrier c} :=
    base_mem_of tS puiseuxBaseUniformizer.property
  have hball : {c : Carrier | baseCarrier c}.Definable LRV {z : Fin (d + 0) → Carrier | ∀ i,
      z i ∈ SpecialTransformations.Section8.rawOpenBall (vfOf 0).val (vfOf 1).val} := by
    have heach (i : Fin (d + 0)) := (SpecialTransformations.Section8.rawOpenBall_definable h0 h1).preimage_comp
      (fun _ : Fin 1 => i)
    convert Set.definable_iInter_of_finite heach using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  have hcoeff : ∀ k, ((fC f).coeff k).val ∈ {c : Carrier | baseCarrier c} := by
    intro k
    rw [fC, MvPolynomial.coeff_map]
    exact base_mem_of _ (const_mem_base _)
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0)
    (S := {c : Carrier | baseCarrier c}) (fC f) hcoeff
  change @Set.DefinableFun Carrier LRV (CanonicalStructure.normalize (M := Carrier)) (Fin d ⊕ Fin 0)
    {c : Carrier | baseCarrier c} (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (fC f)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hp
  have hcodes : {c : Carrier | baseCarrier c}.DefinableMap LRV (codesOf (d := d)) := by
    intro a
    cases a with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i => exact i.elim0
  have hF : {c : Carrier | baseCarrier c}.DefinableFun LRV
      (fun z : Fin (d + 0) → Carrier => iRv (SpecialTransformations.Section5.mvPolynomialCode (fC f) (codesOf z))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (show {c : Carrier | baseCarrier c}.DefinableMap LRV
          (fun z : Fin (d + 0) → Carrier => ![SpecialTransformations.Section5.mvPolynomialCode (fC f) (codesOf z)]) from by
        intro a
        fin_cases a
        exact hp.comp hcodes)
  have hG : {c : Carrier | baseCarrier c}.DefinableFun LRV (fun _ : Fin (d + 0) → Carrier => iRv (vfOf tS).val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (show {c : Carrier | baseCarrier c}.DefinableMap LRV (fun _ : Fin (d + 0) → Carrier => ![(vfOf tS).val]) from by
        intro a
        fin_cases a
        exact LRV.definableFun_const _ ht)
  convert hball.inter (hF.ofPred_eq hG) using 1
  ext z
  simp only [rawMilnor, Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem mixedSorts_zero (i : Fin (d + 0)) : mixedSorts d 0 i = .vf := by
  show Fin.addCases (motive := fun _ => SortTag) (fun _ => SortTag.vf) (fun _ => SortTag.rv)
    (Fin.castAdd 0 i) = SortTag.vf
  exact Fin.addCases_left i

theorem rawMilnor_definableOver :
    DefinableOver {c | baseCarrier c} (mixedSorts d 0) (rawMilnor f) := by
  refine (definableOver_iff_normalized_raw _ _ _).mpr ⟨?_, ?_⟩
  · rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical]
    exact rawMilnor_definable f
  · intro z hz i
    rw [mixedSorts_zero]
    exact (hz.1 i).2.1

/-- Membership in the unit open ball of the concrete model. -/
theorem mem_ball_conc (g : Ser) :
    (Sum.inl g : Carrier) ∈ SpecialTransformations.Section8.rawOpenBall (vfOf 0).val (vfOf 1).val ↔
      0 < ordS g := by
  change (vfOf g).val ∈ OpenBallCodes.rawBall ![(vfOf 0).val, (vfOf 1).val] ↔ _
  rw [OpenBallCodes.rawBall, Set.mem_ofPred_eq, OpenBallCodes.body_realize]
  have hP : OpenBallCodes.Proper ![(vfOf 0).val, (vfOf 1).val] := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact (vfOf 0).property
      · exact (vfOf 1).property
    · intro h
      have h' : vfOf 1 = (0 : VFType (M := Carrier)) := Subtype.ext h
      exact one_ne_zero (taggedFieldEquiv.symm.injective (h'.trans taggedFieldEquiv.symm.map_zero.symm))
  rw [and_iff_right hP, and_iff_right (vfOf g).property]
  have hd : (vfOf g - vfOf 0).val = iVFAdd (vfOf g).val (iVFNeg (vfOf 0).val) := by
    rw [sub_eq_add_neg]; rfl
  change ¬ iLe (iRv (iVFAdd (vfOf g).val (iVFNeg (vfOf 0).val))) (iRv (vfOf 1).val) ↔ _
  rw [← hd]
  change ¬ VFValued.predV (vfOf 1) (vfOf g - vfOf 0) ↔ _
  have h0 : vfOf g - vfOf 0 = vfOf g := by
    rw [show vfOf 0 = 0 from taggedFieldEquiv.symm.map_zero, sub_zero]
  rw [h0, taggedFieldEquiv_valuation, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    (puiseuxValuation ℂ).map_one, not_le]
  change Multiplicative.ofAdd (OrderDual.toDual ((g : HahnSeries ℚ ℂ).orderTop)) <
      Multiplicative.ofAdd (OrderDual.toDual ((0 : ℚ) : WithTop ℚ)) ↔ _
  rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]
  rfl

theorem mixedRaw_zero (p : (Fin d → Ser) × (Fin 0 → RV)) (i : Fin (d + 0)) :
    mixedRaw p i = Sum.inl (p.1 i) := by
  refine Fin.addCases (fun j => ?_) (fun j => j.elim0) i
  rw [mixedRaw, Fin.append_left]
  rfl

/-- The points of `𝒳_f`. -/
theorem mem_mixedSet_milnor (p : (Fin d → Ser) × (Fin 0 → RV)) :
    p ∈ mixedSet (rawMilnor f) ↔ (∀ i, 0 < ordS (p.1 i)) ∧
      rvOfField (MvPolynomial.eval p.1 (MvPolynomial.map puiseuxConstant f)) = rvOfField tS := by
  change mixedRaw p ∈ rawMilnor f ↔ _
  simp only [rawMilnor, Set.mem_ofPred_eq, mixedRaw_zero]
  refine and_congr (forall_congr' fun i => mem_ball_conc (p.1 i)) ?_
  have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (fC f) (codesOf (mixedRaw p))
    (fun i => vfOf (p.1 i)) (fun i => by rw [codesOf, Sum.elim_inl, mixedRaw_zero]; rfl)
  rw [hcode, iRv_val, iRv_val, RingEquiv.apply_symm_apply]
  have he : taggedFieldEquiv (MvPolynomial.eval (fun i => vfOf (p.1 i)) (fC f)) =
      MvPolynomial.eval p.1 (MvPolynomial.map puiseuxConstant f) := by
    rw [fC, MvPolynomial.eval_map, MvPolynomial.eval_map]
    have h := MvPolynomial.eval₂_comp_left taggedFieldEquiv.toRingHom
      (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant) (fun i => vfOf (p.1 i)) f
    have hc : taggedFieldEquiv.toRingHom.comp (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant) =
        puiseuxConstant := RingHom.ext fun c => taggedFieldEquiv.apply_symm_apply _
    have hx : (taggedFieldEquiv.toRingHom ∘ fun i => vfOf (p.1 i)) = p.1 := by
      funext i
      exact taggedFieldEquiv.apply_symm_apply _
    rw [hc, hx] at h
    exact h
  rw [he]
  constructor
  · intro h; exact Sum.inr_injective h
  · intro h; rw [h]

/-! ### Invariance for `β = (1, …, 1)` -/

/-- The cutoffs `β = (1, …, 1)` at level `m`: `b_i = m`. -/
abbrev bOne (m : ℕ+) : Fin d → ℕ := fun _ => (m : ℕ)

theorem ordS_tS : ordS tS = 1 := by
  unfold ordS
  rw [puiseuxRoot_coe, orderTop_single one_ne_zero]
  norm_num

theorem tS_ne_zero : tS ≠ 0 := puiseuxRoot_ne_zero 1

theorem ordS_of_rv_eq {y : Ser} (h : rvOfField y = rvOfField tS) : ordS y = 1 := by
  have h1 := congrArg value h
  rw [rvOfField_value, rvOfField_value] at h1
  exact h1.trans ordS_tS

theorem milnor_invariant_conc (m : ℕ+) : Invariant m (bOne m) (mixedSet (rawMilnor f)) := by
  intro x x' u hx hcongr
  rw [mem_mixedSet_milnor] at hx ⊢
  obtain ⟨hxM, hxf⟩ := hx
  have hdiff : ∀ i, ((1 : ℚ) : WithTop ℚ) < ordS (x i - x' i) := by
    intro i
    rw [lt_ordS_iff]
    intro γ hγ
    have : cf (x i - x' i) γ = cf (x i) γ - cf (x' i) γ := by
      change (x i : HahnSeries ℚ ℂ).coeff γ - (x' i : HahnSeries ℚ ℂ).coeff γ = _
      rfl
    rw [this, hcongr i γ (by rw [lev_self]; exact hγ), sub_self]
  have hx'M : ∀ i, 0 < ordS (x' i) := by
    intro i
    rw [pos_ordS_iff]
    intro γ hγ
    have h1 := hcongr i γ (le_trans hγ (by rw [lev_self]; norm_num))
    rw [← h1]
    exact (pos_ordS_iff (x i)).mp (hxM i) γ hγ
  refine ⟨hx'M, ?_⟩
  set y := MvPolynomial.eval x (MvPolynomial.map puiseuxConstant f)
  set y' := MvPolynomial.eval x' (MvPolynomial.map puiseuxConstant f)
  have hy : ordS y = 1 := ordS_of_rv_eq hxf
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, ordS_zero] at hy
    exact absurd hy (by simp)
  have hlip := poly_lipschitz_conc f (fun i => (hxM i).le) (fun i => (hx'M i).le) hdiff
  have hclose : ordS y < ordS (y' - y) := by
    rw [hy]
    have he : y' - y = -(y - y') := by ring
    rw [he, ordS_neg]
    exact_mod_cast hlip
  rw [rvOfField_eq_of_close hy0 hclose]
  exact hxf

/-! ### The jet set -/

/-- The polynomial `f(Σ_k a_{i,k} s^k) ∈ ℂ[s]`. -/
def jetPoly (m : ℕ+) (a : Fin d → Fin ((m : ℕ) + 1) → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => ∑ k : Fin ((m : ℕ) + 1), Polynomial.C (a i k) * Polynomial.X ^ (k : ℕ)) f

/-- **The jets**: `a_{i,0} = 0` and `f(Σ_k a_{i,k} s^k) ≡ s^m mod s^{m+1}`. -/
def IsJet (m : ℕ+) (a : Fin d → Fin ((m : ℕ) + 1) → ℂ) : Prop :=
  (∀ i, a i 0 = 0) ∧ (∀ j < (m : ℕ), (jetPoly f m a).coeff j = 0) ∧ (jetPoly f m a).coeff m = 1

theorem polyRep_eq_sub (m : ℕ+) (c : Idx (bOne (d := d) m) → ℂ) (i : Fin d) :
    polyRep m (bOne m) c i =
      sub m (∑ k : Fin ((m : ℕ) + 1), Polynomial.C (c ⟨i, k⟩) * Polynomial.X ^ (k : ℕ)) := by
  rw [polyRep, map_sum]
  exact Finset.sum_congr rfl fun k _ => (sub_mono m k _).symm

theorem eval_polyRep (m : ℕ+) (c : Idx (bOne (d := d) m) → ℂ) :
    MvPolynomial.eval (polyRep m (bOne m) c) (MvPolynomial.map puiseuxConstant f) =
      sub m (jetPoly f m (fun i k => c ⟨i, k⟩)) := by
  rw [MvPolynomial.eval_map, jetPoly]
  have h := MvPolynomial.eval₂_comp_left (sub m) Polynomial.C
    (fun i => ∑ k : Fin ((m : ℕ) + 1), Polynomial.C (c ⟨i, k⟩) * Polynomial.X ^ (k : ℕ)) f
  have hc : (sub m).comp Polynomial.C = puiseuxConstant := RingHom.ext fun x => sub_C m x
  rw [hc] at h
  rw [h]
  congr 1
  funext i
  exact polyRep_eq_sub m c i

theorem pos_ordS_polyRep (m : ℕ+) (c : Idx (bOne (d := d) m) → ℂ) (i : Fin d) :
    0 < ordS (polyRep m (bOne m) c i) ↔ c ⟨i, 0⟩ = 0 := by
  rw [pos_ordS_iff]
  constructor
  · intro h
    have := h 0 le_rfl
    have h0 := cf_polyRep_level m (bOne m) c i 0
    simp only [Fin.val_zero, lev, Nat.cast_zero, zero_div] at h0
    rw [← h0]
    exact this
  · intro h γ hγ
    rcases lt_or_eq_of_le hγ with hlt | heq
    · exact polyRep_integral m (bOne m) c i γ hlt
    · have h0 := cf_polyRep_level m (bOne m) c i 0
      simp only [Fin.val_zero, lev, Nat.cast_zero, zero_div] at h0
      rw [heq, h0, h]

theorem rv_sub_eq_tS_iff (m : ℕ+) (g : Polynomial ℂ) :
    rvOfField (sub m g) = rvOfField tS ↔ (∀ j < (m : ℕ), g.coeff j = 0) ∧ g.coeff m = 1 := by
  have ht1 : (tS : HahnSeries ℚ ℂ) ≠ 0 := fun h => tS_ne_zero (Subtype.ext h)
  have htord : (tS : HahnSeries ℚ ℂ).order = 1 := by
    rw [puiseuxRoot_coe, order_single one_ne_zero]; norm_num
  have htlead : (tS : HahnSeries ℚ ℂ).leadingCoeff = 1 := by
    rw [leadingCoeff_eq, htord, puiseuxRoot_coe]; simp
  constructor
  · intro h
    have hg0 := ne_zero_of_rvOfField_eq tS_ne_zero h
    have hg1 : (sub m g : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
    obtain ⟨hord, hlead⟩ := (rvOfField_eq_iff hg0 tS_ne_zero).mp h
    rw [htord] at hord
    rw [htlead, leadingCoeff_eq, hord] at hlead
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← cf_sub_lev m g j]
      apply coeff_eq_zero_of_lt_order
      rw [hord]
      exact lev_lt_one.mpr hj
    · rw [← cf_sub_lev m g m, lev_self]
      exact hlead
  · rintro ⟨hlow, hm⟩
    have hcf1 : cf (sub m g) 1 = 1 := by rw [← lev_self m, cf_sub_lev, hm]
    have hg0 : sub m g ≠ 0 := by
      intro h0
      rw [h0] at hcf1
      exact absurd hcf1 (by change (0 : ℂ) ≠ 1; exact zero_ne_one)
    have hg1 : (sub m g : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
    have hlowall : ∀ γ < (1 : ℚ), cf (sub m g) γ = 0 := by
      intro γ hγ
      by_cases hl : ∃ j : ℕ, γ = lev m j
      · obtain ⟨j, rfl⟩ := hl
        rw [cf_sub_lev]
        exact hlow j (lev_lt_one.mp hγ)
      · push Not at hl
        exact cf_sub_of_not_lev m g γ hl
    have hord : (sub m g : HahnSeries ℚ ℂ).order = 1 := by
      apply le_antisymm
      · exact order_le_of_coeff_ne_zero (by change cf (sub m g) 1 ≠ 0; rw [hcf1]; exact one_ne_zero)
      · by_contra hlt
        push Not at hlt
        exact coeff_order_ne hg1 (hlowall _ hlt)
    refine (rvOfField_eq_iff hg0 tS_ne_zero).mpr ⟨by rw [hord, htord], ?_⟩
    rw [htlead, leadingCoeff_eq, hord]
    exact hcf1

/-- **The coefficient set of the truncation of `𝒳_f` is the jet set.** -/
theorem milnor_coeffSet (m : ℕ+) (c : Idx (bOne (d := d) m) ⊕ Fin 0 → ℂ) :
    c ∈ coeffSet m (bOne m) Fin.elim0 (mixedSet (rawMilnor f)) ↔
      IsJet f m (fun i k => c (.inl ⟨i, k⟩)) := by
  change (polyRep m (bOne m) (fun k => c (.inl k)), labelRep m Fin.elim0 (fun j => c (.inr j))) ∈
    mixedSet (rawMilnor f) ↔ _
  rw [mem_mixedSet_milnor]
  simp only
  rw [eval_polyRep, rv_sub_eq_tS_iff]
  unfold IsJet
  refine and_congr (forall_congr' fun i => pos_ordS_polyRep m _ i) ?_
  rfl

/-- **`𝒳_f[m; (1, …, 1)]` is the jet set**, through `a ↦ (rv(a_{i,k} t^{k/m}))`. -/
theorem milnor_trunc_eq (m : ℕ+) :
    {w | w ∈ truncSet m (bOne m) (mixedSet (rawMilnor f)) ∧
      ∀ j : Fin 0, w (.inr j) ∈ Line (zlev m ((Fin.elim0 : Fin 0 → ℤ) j))} =
      frameOf m (bOne m) Fin.elim0 ''
        {c | IsJet f m (fun i k => c (.inl ⟨i, k⟩))} := by
  rw [truncSet_pattern_eq m (bOne m) Fin.elim0 _ (milnor_invariant_conc f m)]
  congr 1
  ext c
  exact milnor_coeffSet f m c

end DiamondIntegral.Section8.Truncation
