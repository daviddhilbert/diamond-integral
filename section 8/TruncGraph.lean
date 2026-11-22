import «section 8».TruncInvariance

/-! Congruence modulo `𝔪_β` in the concrete model.

* `ordS_pow`: `ordS (x^k) = k • ordS x`.
* `congrSet m b k`: pairs of raw mixed tuples `(p, p')` with `v(x_i − x'_i) > b_i/m` and equal labels;
  definable over `ℂ((t))` (`congrSet_definable`), written as `v((x_i − x'_i)^m) > v(t^{b_i})`.
* `mem_congrSet_iff`: its meaning on concrete points; `truncOf_eq_iff`: two rational integral points
  have the same truncation iff they are congruent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section4 DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

local instance graphStructure : LRV.Structure Carrier := canonicalInterpret
local instance graphModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

theorem ordS_pow (x : Ser) (k : ℕ) : ordS (x ^ k) = k • ordS x := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    change ((1 : Ser) : HahnSeries ℚ ℂ).orderTop = 0
    exact orderTop_one
  | succ k ih =>
    rw [pow_succ, succ_nsmul, ← ih]
    exact orderTop_mul _ _

/-- `¬ iLe (rv w) (rv u)` in the concrete model: `ordS u < ordS w`. -/
theorem not_iLe_rv_inl (w u : Ser) :
    ¬ iLe (iRv (Sum.inl w : Carrier)) (iRv (Sum.inl u : Carrier)) ↔ ordS u < ordS w := by
  rw [iRv_inl, iRv_inl]
  change ¬ iLe (rvTag (rvOfField w)).val (rvTag (rvOfField u)).val ↔ _
  rw [iLe_rvTag, rvOfField_value, rvOfField_value, not_le]
  rfl

variable {n : ℕ} (m : ℕ+) (b : Fin n → ℕ)

/-- `t^b` as a field element of the concrete model. -/
abbrev tPow (k : ℕ) : Ser := tS ^ k

theorem tPow_mem (k : ℕ) : baseCarrier (Sum.inl (tPow k) : Carrier) :=
  pow_mem puiseuxBaseUniformizer.property k

theorem ordS_tPow (k : ℕ) : ordS (tPow k) = (k : ℚ) := by
  rw [ordS_pow, ordS_tS]
  simp

/-- Congruence of two field elements modulo `𝔪_{b/m}`. -/
theorem congr_iff_pow (x y : Ser) (k : ℕ) :
    ((lev m k : ℚ) : WithTop ℚ) < ordS (x - y) ↔ ordS (tPow k) < ordS ((x - y) ^ (m : ℕ)) := by
  rw [ordS_tPow, ordS_pow]
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  induction ordS (x - y) using WithTop.recTopCoe with
  | top =>
    have ht : (m : ℕ) • (⊤ : WithTop ℚ) = ⊤ := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero m.ne_zero
      rw [hj, succ_nsmul, WithTop.add_top]
    rw [ht]
    exact iff_of_true (WithTop.coe_lt_top _) (WithTop.coe_lt_top _)
  | coe o =>
    rw [← WithTop.coe_nsmul, WithTop.coe_lt_coe, WithTop.coe_lt_coe, nsmul_eq_mul, lev]
    constructor
    · intro h1
      have := mul_lt_mul_of_pos_left h1 hm
      rwa [mul_div_cancel₀ _ hm.ne'] at this
    · intro h1
      rw [div_lt_iff₀ hm]
      linarith

/-! ### The congruence set -/

variable {k : ℕ}

/-- Left and right VF and label indices of a pair of raw mixed tuples. -/
abbrev lVF (i : Fin n) : Fin ((n + k) + (n + k)) := Fin.castAdd (n + k) (Fin.castAdd k i)
abbrev rVF (i : Fin n) : Fin ((n + k) + (n + k)) := Fin.natAdd (n + k) (Fin.castAdd k i)
abbrev lRV (j : Fin k) : Fin ((n + k) + (n + k)) := Fin.castAdd (n + k) (Fin.natAdd n j)
abbrev rRV (j : Fin k) : Fin ((n + k) + (n + k)) := Fin.natAdd (n + k) (Fin.natAdd n j)

/-- The polynomial `(X₀ − X₁)^m` with coefficients in the field sort of the concrete model. -/
def diffPow : MvPolynomial (Fin 2) (VFType (M := Carrier)) :=
  MvPolynomial.map (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant)
    ((MvPolynomial.X 0 - MvPolynomial.X 1) ^ (m : ℕ) : MvPolynomial (Fin 2) ℂ)

/-- The code of `(x − y)^m` for the VF coordinate `i`. -/
def diffCode (i : Fin n) (z : Fin ((n + k) + (n + k)) → Carrier) : Carrier :=
  SpecialTransformations.Section5.mvPolynomialCode (diffPow m) (Sum.elim ![z (lVF i), z (rVF i)] Fin.elim0)

/-- **Congruence modulo `𝔪_β`** of the two halves of a pair of raw mixed tuples. -/
def congrSet : Set (Fin ((n + k) + (n + k)) → Carrier) :=
  {z | (∀ i, ¬ iLe (iRv (diffCode (k := k) m i z)) (iRv (Sum.inl (tPow (b i)) : Carrier))) ∧
    ∀ j, z (lRV j) = z (rRV j)}

theorem diffPow_coeff_mem (d : Fin 2 →₀ ℕ) : ((diffPow m).coeff d).val ∈ {c : Carrier | baseCarrier c} := by
  rw [diffPow, MvPolynomial.coeff_map]
  exact base_mem_of _ (const_mem_base _)

theorem congrSet_definable : {c | baseCarrier c}.Definable LRV (congrSet (k := k) m b) := by
  have hp := SpecialTransformations.Section5.mvPolynomialCode_definable (m := 0)
    (S := {c : Carrier | baseCarrier c}) (diffPow m) (diffPow_coeff_mem m)
  change @Set.DefinableFun Carrier LRV (CanonicalStructure.normalize (M := Carrier)) (Fin 2 ⊕ Fin 0)
    {c : Carrier | baseCarrier c} (SpecialTransformations.Section5.mvPolynomialCode (m := 0) (diffPow m)) at hp
  rw [SpecialTransformations.Section4.canonical_normalize_eq canonicalInterpret_isCanonical] at hp
  have hcode (i : Fin n) : {c : Carrier | baseCarrier c}.DefinableFun LRV (diffCode (k := k) m i) := by
    have hinner : {c : Carrier | baseCarrier c}.DefinableMap LRV
        (fun z : Fin ((n + k) + (n + k)) → Carrier => (Sum.elim ![z (lVF i), z (rVF i)] Fin.elim0 :
          Fin 2 ⊕ Fin 0 → Carrier)) := by
      intro a
      rcases a with a | a
      · fin_cases a
        · exact Set.DefinableFun.proj LRV
        · exact Set.DefinableFun.proj LRV
      · exact a.elim0
    change {c : Carrier | baseCarrier c}.DefinableFun LRV (fun z : Fin ((n + k) + (n + k)) → Carrier =>
      SpecialTransformations.Section5.mvPolynomialCode (diffPow m)
        ((fun z : Fin ((n + k) + (n + k)) → Carrier => (Sum.elim ![z (lVF i), z (rVF i)] Fin.elim0 :
          Fin 2 ⊕ Fin 0 → Carrier)) z))
    exact hp.comp hinner
  have hrv (i : Fin n) : {c : Carrier | baseCarrier c}.DefinableFun LRV
      (fun z : Fin ((n + k) + (n + k)) → Carrier => iRv (diffCode (k := k) m i z)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (fun a => by fin_cases a; exact hcode i)
  have hconst (i : Fin n) : {c : Carrier | baseCarrier c}.DefinableFun LRV
      (fun _ : Fin ((n + k) + (n + k)) → Carrier => iRv (Sum.inl (tPow (b i)) : Carrier)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := Carrier) (L := LRV) Fn.rvMap)).comp
      (fun a => by fin_cases a; exact LRV.definableFun_const _ (tPow_mem (b i)))
  have hle (i : Fin n) : {c : Carrier | baseCarrier c}.Definable LRV
      {z : Fin ((n + k) + (n + k)) → Carrier | iLe (iRv (diffCode (k := k) m i z)) (iRv (Sum.inl (tPow (b i)) : Carrier))} := by
    have h := (raw_le_definable {c : Carrier | baseCarrier c}).preimage_map
      (F := fun z : Fin ((n + k) + (n + k)) → Carrier => ![iRv (diffCode (k := k) m i z), iRv (Sum.inl (tPow (b i)) : Carrier)])
      (fun a => by fin_cases a; exacts [hrv i, hconst i])
    exact h
  have h1 : {c : Carrier | baseCarrier c}.Definable LRV {z : Fin ((n + k) + (n + k)) → Carrier |
      ∀ i, ¬ iLe (iRv (diffCode (k := k) m i z)) (iRv (Sum.inl (tPow (b i)) : Carrier))} := by
    convert Set.definable_iInter_of_finite (fun i => (hle i).compl) using 1
    ext z
    simp
  have h2 : {c : Carrier | baseCarrier c}.Definable LRV {z : Fin ((n + k) + (n + k)) → Carrier |
      ∀ j, z (lRV j) = z (rRV j)} := by
    convert Set.definable_iInter_of_finite (fun j : Fin k =>
      (Set.DefinableFun.proj (L := LRV) (A := {c : Carrier | baseCarrier c}) (i := lRV (n := n) j)).ofPred_eq
        (Set.DefinableFun.proj (L := LRV) (A := {c : Carrier | baseCarrier c}) (i := rRV (n := n) j))) using 1
    ext z
    simp
  convert h1.inter h2 using 1
  ext z
  rfl

theorem append_mixedRaw_l (p p' : (Fin n → Ser) × (Fin k → RV)) (i : Fin n) :
    Fin.append (mixedRaw p) (mixedRaw p') (lVF i) = Sum.inl (p.1 i) := by
  rw [lVF, Fin.append_left, mixedRaw, Fin.append_left]

theorem append_mixedRaw_r (p p' : (Fin n → Ser) × (Fin k → RV)) (i : Fin n) :
    Fin.append (mixedRaw p) (mixedRaw p') (rVF i) = Sum.inl (p'.1 i) := by
  rw [rVF, Fin.append_right, mixedRaw, Fin.append_left]

theorem append_mixedRaw_lRV (p p' : (Fin n → Ser) × (Fin k → RV)) (j : Fin k) :
    Fin.append (mixedRaw p) (mixedRaw p') (lRV j) = Sum.inr (p.2 j) := by
  rw [lRV, Fin.append_left, mixedRaw, Fin.append_right]

theorem append_mixedRaw_rRV (p p' : (Fin n → Ser) × (Fin k → RV)) (j : Fin k) :
    Fin.append (mixedRaw p) (mixedRaw p') (rRV j) = Sum.inr (p'.2 j) := by
  rw [rRV, Fin.append_right, mixedRaw, Fin.append_right]

theorem diffCode_mixedRaw (p p' : (Fin n → Ser) × (Fin k → RV)) (i : Fin n) :
    diffCode (k := k) m i (Fin.append (mixedRaw p) (mixedRaw p')) = Sum.inl ((p.1 i - p'.1 i) ^ (m : ℕ)) := by
  unfold diffCode
  rw [append_mixedRaw_l, append_mixedRaw_r]
  have hcode := SpecialTransformations.Section5.mvPolynomialCode_eq (diffPow m)
    (Sum.elim ![(Sum.inl (p.1 i) : Carrier), Sum.inl (p'.1 i)] Fin.elim0) ![vfOf (p.1 i), vfOf (p'.1 i)]
    (fun a => by fin_cases a <;> rfl)
  rw [hcode]
  have he : taggedFieldEquiv (MvPolynomial.eval ![vfOf (p.1 i), vfOf (p'.1 i)] (diffPow m)) =
      (p.1 i - p'.1 i) ^ (m : ℕ) := by
    rw [diffPow, MvPolynomial.eval_map]
    have h := MvPolynomial.eval₂_comp_left taggedFieldEquiv.toRingHom
      (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant) ![vfOf (p.1 i), vfOf (p'.1 i)]
      ((MvPolynomial.X 0 - MvPolynomial.X 1) ^ (m : ℕ) : MvPolynomial (Fin 2) ℂ)
    have hc : taggedFieldEquiv.toRingHom.comp (taggedFieldEquiv.symm.toRingHom.comp puiseuxConstant) =
        puiseuxConstant := RingHom.ext fun c => taggedFieldEquiv.apply_symm_apply _
    have hx : (taggedFieldEquiv.toRingHom ∘ ![vfOf (p.1 i), vfOf (p'.1 i)]) = ![p.1 i, p'.1 i] := by
      funext a
      fin_cases a <;> exact taggedFieldEquiv.apply_symm_apply _
    rw [hc, hx] at h
    change taggedFieldEquiv.toRingHom _ = _
    rw [h]
    simp
  rw [← he]
  exact (vfType_tag _).symm

/-- **Congruence on concrete points.** -/
theorem mem_congrSet_iff (p p' : (Fin n → Ser) × (Fin k → RV)) :
    Fin.append (mixedRaw p) (mixedRaw p') ∈ congrSet (k := k) m b ↔
      (∀ i, ((lev m (b i) : ℚ) : WithTop ℚ) < ordS (p.1 i - p'.1 i)) ∧ ∀ j, p.2 j = p'.2 j := by
  simp only [congrSet, Set.mem_ofPred_eq, diffCode_mixedRaw, append_mixedRaw_lRV, append_mixedRaw_rRV]
  refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun j => ⟨fun h => Sum.inr_injective h,
    fun h => by rw [h]⟩)
  rw [not_iLe_rv_inl, congr_iff_pow]

/-- Two rational integral points have the same truncation iff they are congruent. -/
theorem truncOf_eq_iff {p p' : (Fin n → Ser) × (Fin k → RV)} (hp : RI m p) (hp' : RI m p') :
    truncOf m b p = truncOf m b p' ↔
      (∀ i, ((lev m (b i) : ℚ) : WithTop ℚ) < ordS (p.1 i - p'.1 i)) ∧ ∀ j, p.2 j = p'.2 j := by
  have hcf : ∀ (x y : Ser), IsRational m x → IsIntegral x → IsRational m y → IsIntegral y → ∀ (B : ℕ),
      ((∀ j : Fin (B + 1), cf x (lev m j) = cf y (lev m j)) ↔ ((lev m B : ℚ) : WithTop ℚ) < ordS (x - y)) := by
    intro x y hx hxi hy hyi B
    rw [lt_ordS_iff]
    have hd : ∀ γ, cf (x - y) γ = cf x γ - cf y γ := fun γ => rfl
    constructor
    · intro h γ hγ
      rw [hd, sub_eq_zero]
      by_cases hγ0 : γ < 0
      · rw [hxi γ hγ0, hyi γ hγ0]
      · by_cases hl : ∃ j : ℕ, γ = lev m j
        · obtain ⟨j, rfl⟩ := hl
          have hjB : j ≤ B := by
            by_contra hlt
            push Not at hlt
            exact absurd hγ (not_le.mpr (lev_lt_lev hlt))
          exact h ⟨j, Nat.lt_succ_of_le hjB⟩
        · push Not at hl
          have hx0 : cf x γ = 0 := by
            by_contra hne
            obtain ⟨z, hz⟩ := hx γ hne
            have hz0 : 0 ≤ z := by
              by_contra hneg
              push Not at hneg
              have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
              exact hγ0 (by rw [hz]; exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) hm)
            exact hl z.toNat (by rw [hz, lev]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hz0).symm)
          have hy0 : cf y γ = 0 := by
            by_contra hne
            obtain ⟨z, hz⟩ := hy γ hne
            have hz0 : 0 ≤ z := by
              by_contra hneg
              push Not at hneg
              have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
              exact hγ0 (by rw [hz]; exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) hm)
            exact hl z.toNat (by rw [hz, lev]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hz0).symm)
          rw [hx0, hy0]
    · intro h j
      have := h (lev m j) (by
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp j.isLt) with hlt | heq
        · exact (lev_lt_lev hlt).le
        · rw [heq])
      rw [hd, sub_eq_zero] at this
      exact this
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · refine (hcf _ _ (hp.1 i).1 (hp.1 i).2 (hp'.1 i).1 (hp'.1 i).2 (b i)).mp fun j => ?_
      have := congrFun h (εt b k (.inl ⟨i, j⟩))
      simp only [truncOf, Equiv.symm_apply_apply, Sum.elim_inl, truncPoint] at this
      have h2 := congrArg (fun r => lineCoeff (taggedRVEquiv r)) this
      rw [show taggedRVEquiv (rvTag _) = _ from taggedRVEquiv.apply_symm_apply _,
        show taggedRVEquiv (rvTag _) = _ from taggedRVEquiv.apply_symm_apply _,
        lineCoeff_coeffRV, lineCoeff_coeffRV] at h2
      exact h2
    · have := congrFun h (εt b k (.inr j))
      simp only [truncOf, Equiv.symm_apply_apply, Sum.elim_inr] at this
      exact taggedRVEquiv.symm.injective this
  · rintro ⟨h1, h2⟩
    funext a
    simp only [truncOf]
    rcases hs : (εt b k).symm a with ⟨i, j⟩ | j
    · simp only [Sum.elim_inl, truncPoint]
      have := (hcf _ _ (hp.1 i).1 (hp.1 i).2 (hp'.1 i).1 (hp'.1 i).2 (b i)).mpr (h1 i) j
      rw [this]
    · simp only [Sum.elim_inr]
      rw [h2 j]

end DiamondIntegral.Section8.Truncation
