import «section 8».TruncSets

/-! Valuations, leading terms and polynomials in `ℂ((t^{1/m}))` for the jet comparison.

* `ordS x = orderTop x ∈ ℚ ∪ {∞}`; `poly_lipschitz_conc`: a polynomial with complex coefficients is
  `1`-Lipschitz on `𝒪^d` for `ordS`.
* `rvOfField_eq_iff`: two nonzero series have the same `rv` iff they have the same order and the
  same leading coefficient; `rvOfField_eq_of_close`.
* `sub m : ℂ[s] →+* ℂ{{t}}`, `s ↦ t^{1/m}`; `cf_sub`: the coefficient of `t^{j/m}` of `sub g` is the
  coefficient of `s^j` in `g`. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical HahnSeries
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

/-! ### Orders -/

/-- The order of a series, `∞` for `0`. -/
def ordS (x : Ser) : WithTop ℚ := (x : HahnSeries ℚ ℂ).orderTop

theorem ordS_zero : ordS 0 = ⊤ := orderTop_zero

theorem ordS_add (x y : Ser) : min (ordS x) (ordS y) ≤ ordS (x + y) := min_orderTop_le_orderTop_add

theorem ordS_neg (x : Ser) : ordS (-x) = ordS x := orderTop_neg

theorem ordS_sub (x y : Ser) : min (ordS x) (ordS y) ≤ ordS (x - y) := by
  rw [sub_eq_add_neg, ← ordS_neg y]
  exact ordS_add x (-y)

theorem ordS_mul (x y : Ser) : ordS x + ordS y ≤ ordS (x * y) := orderTop_add_le_mul

theorem ordS_const (c : ℂ) : 0 ≤ ordS (puiseuxConstant c) := by
  unfold ordS
  rw [puiseuxConstant_coe]
  by_cases hc : c = 0
  · rw [hc, map_zero, orderTop_zero]
    exact le_top
  · rw [C_apply, orderTop_single hc]
    rfl

/-- `γ < ordS x` iff all coefficients of `x` at levels `≤ γ` vanish. -/
theorem lt_ordS_iff (x : Ser) (γ : ℚ) : (γ : WithTop ℚ) < ordS x ↔ ∀ γ' ≤ γ, cf x γ' = 0 := by
  constructor
  · intro h γ' hγ'
    exact coeff_eq_zero_of_lt_orderTop (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hγ') h)
  · intro h
    by_contra hle
    push Not at hle
    have hx : x ≠ 0 := by
      intro h0
      rw [h0, ordS_zero] at hle
      exact absurd hle (by simp)
    have hx' : (x : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    have ho : ordS x = ((x : HahnSeries ℚ ℂ).order : WithTop ℚ) :=
      (order_eq_orderTop_of_ne_zero hx').symm
    rw [ho, WithTop.coe_le_coe] at hle
    exact coeff_order_ne hx' (h _ hle)

/-- Strict version with `0`: `0 < ordS x` iff all coefficients at levels `≤ 0` vanish. -/
theorem pos_ordS_iff (x : Ser) : 0 < ordS x ↔ ∀ γ' ≤ (0 : ℚ), cf x γ' = 0 := by
  have := lt_ordS_iff x 0
  simpa using this

/-! ### The Lipschitz estimate -/

/-- On `𝒪^d`, a polynomial with complex coefficients is `1`-Lipschitz. -/
theorem poly_lipschitz_conc {d : ℕ} (g : MvPolynomial (Fin d) ℂ) {x y : Fin d → Ser}
    (hx : ∀ i, 0 ≤ ordS (x i)) (hy : ∀ i, 0 ≤ ordS (y i)) {γ : ℚ}
    (hxy : ∀ i, (γ : WithTop ℚ) < ordS (x i - y i)) :
    (γ : WithTop ℚ) < ordS (MvPolynomial.eval x (MvPolynomial.map puiseuxConstant g) -
      MvPolynomial.eval y (MvPolynomial.map puiseuxConstant g)) := by
  have hint : ∀ (p : MvPolynomial (Fin d) ℂ) (z : Fin d → Ser), (∀ i, 0 ≤ ordS (z i)) →
      0 ≤ ordS (MvPolynomial.eval z (MvPolynomial.map puiseuxConstant p)) := by
    intro p z hz
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.map_C, MvPolynomial.eval_C]
      exact ordS_const a
    | add p q hp hq =>
      rw [RingHom.map_add, RingHom.map_add]
      exact le_trans (le_min hp hq) (ordS_add _ _)
    | mul_X p i hp =>
      rw [RingHom.map_mul, MvPolynomial.map_X, RingHom.map_mul, MvPolynomial.eval_X]
      exact le_trans (by simpa using add_le_add hp (hz i)) (ordS_mul _ _)
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.eval_C, sub_self, ordS_zero]
    exact WithTop.coe_lt_top γ
  | add p q hp hq =>
    rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, add_sub_add_comm]
    exact lt_of_lt_of_le (lt_min hp hq) (ordS_add _ _)
  | mul_X p i hp =>
    rw [RingHom.map_mul, MvPolynomial.map_X, RingHom.map_mul, RingHom.map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_X]
    set u := MvPolynomial.eval x (MvPolynomial.map puiseuxConstant p)
    set w := MvPolynomial.eval y (MvPolynomial.map puiseuxConstant p)
    have hw : 0 ≤ ordS w := hint p y hy
    have he : u * x i - w * y i = (u - w) * x i + w * (x i - y i) := by ring
    rw [he]
    refine lt_of_lt_of_le (lt_min ?_ ?_) (ordS_add _ _)
    · exact lt_of_lt_of_le (lt_of_lt_of_le hp (le_add_of_nonneg_right (hx i))) (ordS_mul _ _)
    · exact lt_of_lt_of_le (lt_of_lt_of_le (hxy i) (le_add_of_nonneg_left hw)) (ordS_mul _ _)

/-! ### `rv` and leading terms -/

theorem rvOfField_of_ne {y : Ser} (hy : y ≠ 0) :
    rvOfField y = some (Multiplicative.ofAdd (y : HahnSeries ℚ ℂ).order,
      Units.mk0 (y : HahnSeries ℚ ℂ).leadingCoeff
        (leadingCoeff_ne_zero.mpr (fun h => hy (Subtype.ext h)))) := by
  rw [rvOfField, RVCalc.rv_of_ne hy]
  change some (puiseuxRVUnitEquiv (QuotientGroup.mk' _ (Units.mk0 y hy))) = _
  rw [puiseuxRVUnitEquiv_mk]
  rfl

/-- Two nonzero series have the same `rv` iff they have the same order and leading coefficient. -/
theorem rvOfField_eq_iff {y y' : Ser} (hy : y ≠ 0) (hy' : y' ≠ 0) :
    rvOfField y = rvOfField y' ↔ (y : HahnSeries ℚ ℂ).order = (y' : HahnSeries ℚ ℂ).order ∧
      (y : HahnSeries ℚ ℂ).leadingCoeff = (y' : HahnSeries ℚ ℂ).leadingCoeff := by
  rw [rvOfField_of_ne hy, rvOfField_of_ne hy']
  constructor
  · intro h
    have h' := Option.some.inj h
    exact ⟨Multiplicative.ofAdd.injective (congrArg Prod.fst h'), congrArg Units.val (congrArg Prod.snd h')⟩
  · rintro ⟨h1, h2⟩
    congr 1
    exact Prod.ext (by rw [h1]) (Units.ext h2)

theorem ne_zero_of_rvOfField_eq {y y' : Ser} (hy : y ≠ 0) (h : rvOfField y' = rvOfField y) : y' ≠ 0 := by
  intro h0
  rw [h0, rvOfField_zero', rvOfField_of_ne hy] at h
  exact absurd h (by simp)

/-- If `y` and `y'` are close relative to the order of `y`, they have the same `rv`. -/
theorem rvOfField_eq_of_close {y y' : Ser} (hy : y ≠ 0) (h : ordS y < ordS (y' - y)) :
    rvOfField y' = rvOfField y := by
  have hy1 : (y : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have he : (y' : HahnSeries ℚ ℂ) = (y : HahnSeries ℚ ℂ) + ((y' - y : Ser) : HahnSeries ℚ ℂ) := by
    change _ = _ + ((y' : HahnSeries ℚ ℂ) - (y : HahnSeries ℚ ℂ))
    ring
  have hord : (y' : HahnSeries ℚ ℂ).orderTop = (y : HahnSeries ℚ ℂ).orderTop := by
    rw [he]; exact orderTop_add_eq_left h
  have hlead : (y' : HahnSeries ℚ ℂ).leadingCoeff = (y : HahnSeries ℚ ℂ).leadingCoeff := by
    rw [he]; exact leadingCoeff_add_eq_left h
  have hy'0 : y' ≠ 0 := by
    intro h0
    have : (y' : HahnSeries ℚ ℂ).orderTop = ⊤ := by rw [h0]; exact orderTop_zero
    rw [this, ← order_eq_orderTop_of_ne_zero hy1] at hord
    exact WithTop.top_ne_coe hord
  have hy'1 : (y' : HahnSeries ℚ ℂ) ≠ 0 := fun h0 => hy'0 (Subtype.ext h0)
  refine (rvOfField_eq_iff hy'0 hy).mpr ⟨?_, hlead⟩
  rw [← order_eq_orderTop_of_ne_zero hy'1, ← order_eq_orderTop_of_ne_zero hy1] at hord
  exact WithTop.coe_injective hord

/-! ### Substitution `s ↦ t^{1/m}` -/

/-- `ℂ[s] → ℂ{{t}}`, `s ↦ t^{1/m}`. -/
def sub (m : ℕ+) : Polynomial ℂ →+* Ser := Polynomial.eval₂RingHom puiseuxConstant (puiseuxRoot m)

theorem sub_eq_sum (m : ℕ+) (g : Polynomial ℂ) :
    sub m g = ∑ j ∈ Finset.range (g.natDegree + 1), mono m j (g.coeff j) := by
  change Polynomial.eval₂ puiseuxConstant (puiseuxRoot m) g = _
  rw [Polynomial.eval₂_eq_sum_range]
  rfl

/-- The coefficient of `t^γ` in `sub g`. -/
theorem cf_sub (m : ℕ+) (g : Polynomial ℂ) (γ : ℚ) :
    cf (sub m g) γ = if h : ∃ j : ℕ, γ = lev m j then g.coeff (Classical.choose h) else 0 := by
  rw [sub_eq_sum, cf_sum]
  split_ifs with h
  · have hj := Classical.choose_spec h
    set j := Classical.choose h
    by_cases hjd : j < g.natDegree + 1
    · rw [Finset.sum_eq_single j]
      · rw [cf_mono, if_pos hj]
      · intro k _ hk
        rw [cf_mono, if_neg]
        intro hγk
        exact hk (lev_injective m (hγk.symm.trans hj))
      · intro hjn
        exact absurd (Finset.mem_range.mpr hjd) hjn
    · have hcoeff : g.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hcoeff]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [cf_mono, if_neg]
      intro hγk
      have := lev_injective m (hγk.symm.trans hj)
      rw [Finset.mem_range] at hk
      omega
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [cf_mono, if_neg]
    intro hγk
    exact h ⟨k, hγk⟩

theorem cf_sub_lev (m : ℕ+) (g : Polynomial ℂ) (j : ℕ) : cf (sub m g) (lev m j) = g.coeff j := by
  rw [cf_sub, dif_pos ⟨j, rfl⟩]
  congr 1
  exact (lev_injective m (Classical.choose_spec (⟨j, rfl⟩ : ∃ k : ℕ, lev m j = lev m k))).symm

theorem cf_sub_of_not_lev (m : ℕ+) (g : Polynomial ℂ) (γ : ℚ) (h : ∀ j : ℕ, γ ≠ lev m j) :
    cf (sub m g) γ = 0 := by
  rw [cf_sub, dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj

theorem sub_C (m : ℕ+) (c : ℂ) : sub m (Polynomial.C c) = puiseuxConstant c := Polynomial.eval₂_C _ _

theorem sub_X (m : ℕ+) : sub m Polynomial.X = puiseuxRoot m := Polynomial.eval₂_X _ _

theorem sub_mono (m : ℕ+) (j : ℕ) (c : ℂ) :
    sub m (Polynomial.C c * Polynomial.X ^ j) = mono m j c := by
  rw [map_mul, map_pow, sub_C, sub_X]
  rfl

theorem lev_self (m : ℕ+) : lev m (m : ℕ) = 1 := by
  rw [lev]
  have hm : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  field_simp

theorem lev_lt_one {m : ℕ+} {j : ℕ} : lev m j < 1 ↔ j < (m : ℕ) := by
  rw [← lev_self m]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases Nat.lt_or_eq_of_le hge with hlt | heq
    · exact absurd h (not_lt.mpr (lev_lt_lev hlt).le)
    · rw [heq] at h; exact lt_irrefl _ h
  · exact fun h => lev_lt_lev h

end DiamondIntegral.Section8.Truncation
