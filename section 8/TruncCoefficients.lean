import «section 8».Truncation
import FubiniTheorems.Decomposition.FiniteKummerFrames
import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxRVActions
import Mathlib.RingTheory.Polynomial.Basic

/-! Polynomials at polynomial points of `ℂ((t^{1/m}))`.

* `ratSubring m`: the subring `ℂ((t^{1/m}))` of the Puiseux series.
* `IsFam m y`: a family `y : (σ → ℂ) → ℂ{{t}}` of `m`-rational series whose coefficients are
  polynomials in the parameter `c`, and vanish below a fixed level.
* `PolyPoint`: a point whose coordinates are `Σ_k c_{var k} t^{lvl k / m}`; `fam_poly`: a polynomial
  over `ℂ((t^{1/m}))` evaluated at such a point is a family in this sense.
* `exists_bound`: by Hilbert's basis theorem, if the coefficients of a family vanish at `c` up to a
  level `R` (independent of `c`), they all vanish.
* `rvOfField_eq_linePoint`: `rv` of a rational series with first nonzero coefficient at level `r` is
  `rv(a t^{r/m})`, `a` that coefficient. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical HahnSeries
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

/-! ### The subring `ℂ((t^{1/m}))` -/

theorem cf_mul_ne_zero {x y : Ser} {γ : ℚ} (h : cf (x * y) γ ≠ 0) :
    ∃ a b : ℚ, cf x a ≠ 0 ∧ cf y b ≠ 0 ∧ a + b = γ := by
  have hmem : γ ∈ ((x : HahnSeries ℚ ℂ) * (y : HahnSeries ℚ ℂ)).support := h
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (support_mul_subset hmem)
  exact ⟨a, b, ha, hb, hab⟩

/-- `ℂ((t^{1/m}))`. -/
def ratSubring (m : ℕ+) : Subring Ser where
  carrier := {x | IsRational m x}
  zero_mem' := fun γ h => absurd rfl h
  one_mem' := by
    intro γ h
    by_cases hγ : γ = 0
    · exact ⟨0, by rw [hγ]; simp⟩
    · have h1 : cf (1 : Ser) γ = 0 := by
        change (1 : HahnSeries ℚ ℂ).coeff γ = 0
        rw [coeff_one]
        simp [hγ]
      exact absurd h1 h
  add_mem' := by
    intro x y hx hy γ h
    by_cases hxγ : cf x γ = 0
    · have : cf y γ ≠ 0 := fun hy0 => h (by rw [cf_add, hxγ, hy0, add_zero])
      exact hy γ this
    · exact hx γ hxγ
  neg_mem' := by
    intro x hx γ h
    have : cf (-x) γ = -cf x γ := coeff_neg
    exact hx γ (fun h0 => h (by rw [this, h0, neg_zero]))
  mul_mem' := by
    intro x y hx hy γ h
    obtain ⟨a, b, ha, hb, rfl⟩ := cf_mul_ne_zero h
    obtain ⟨z, rfl⟩ := hx a ha
    obtain ⟨w, rfl⟩ := hy b hb
    exact ⟨z + w, by push_cast; ring⟩

theorem coeff_order_ne {x : HahnSeries ℚ ℂ} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  fun h => hx (coeff_order_eq_zero.mp h)

theorem mem_ratSubring {m : ℕ+} {x : Ser} : x ∈ ratSubring m ↔ IsRational m x := Iff.rfl

theorem mono_rational (m : ℕ+) (j : ℕ) (c : ℂ) : IsRational m (mono m j c) := by
  intro γ h
  rw [cf_mono] at h
  by_cases hγ : γ = lev m j
  · exact ⟨(j : ℤ), by rw [hγ, lev]; push_cast; rfl⟩
  · rw [if_neg hγ] at h
    exact absurd rfl h

/-! ### Families with polynomial coefficients -/

variable {σ : Type}

/-- The level `r/m`, `r ∈ ℤ`. -/
def zlev (m : ℕ+) (r : ℤ) : ℚ := (r : ℚ) / ((m : ℕ) : ℚ)

theorem zlev_natCast (m : ℕ+) (j : ℕ) : zlev m (j : ℤ) = lev m j := by
  rw [zlev, lev]; push_cast; rfl

theorem zlev_sub (m : ℕ+) (r : ℤ) (j : ℕ) : zlev m (r - j) + lev m j = zlev m r := by
  rw [zlev, zlev, lev]; push_cast; ring

theorem zlev_lt {m : ℕ+} {r s : ℤ} (h : r < s) : zlev m r < zlev m s := by
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  exact div_lt_div_of_pos_right (by exact_mod_cast h) hm

theorem zlev_injective (m : ℕ+) : Function.Injective (zlev m) := by
  intro r s h
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact absurd h (zlev_lt hrs).ne
  · exact hrs
  · exact absurd h.symm (zlev_lt hrs).ne

/-- A family of `m`-rational series whose coefficients are polynomials in `c`, zero below `r₀`. -/
def IsFam (m : ℕ+) (y : (σ → ℂ) → Ser) : Prop :=
  ∃ (r₀ : ℤ) (Q : ℤ → MvPolynomial σ ℂ), (∀ r, r < r₀ → Q r = 0) ∧
    ∀ c, IsRational m (y c) ∧ ∀ r : ℤ, cf (y c) (zlev m r) = MvPolynomial.eval c (Q r)

theorem isFam_const (m : ℕ+) (a : Ser) (ha : IsRational m a) : IsFam m (fun _ : σ → ℂ => a) := by
  by_cases h0 : a = 0
  · subst h0
    exact ⟨0, fun _ => 0, fun _ _ => rfl, fun c => ⟨ha, fun r => by rw [map_zero]; rfl⟩⟩
  · have ha' : (a : HahnSeries ℚ ℂ) ≠ 0 := fun h => h0 (Subtype.ext h)
    obtain ⟨z, hz⟩ := ha (a : HahnSeries ℚ ℂ).order (coeff_order_ne ha')
    refine ⟨z, fun r => MvPolynomial.C (cf a (zlev m r)), fun r hr => ?_, fun c =>
      ⟨ha, fun r => by rw [MvPolynomial.eval_C]⟩⟩
    have hlt : zlev m r < (a : HahnSeries ℚ ℂ).order := by
      rw [hz]; exact zlev_lt hr
    change MvPolynomial.C (cf a (zlev m r)) = 0
    rw [show cf a (zlev m r) = 0 from coeff_eq_zero_of_lt_order hlt, map_zero]

theorem isFam_add {m : ℕ+} {y y' : (σ → ℂ) → Ser} (hy : IsFam m y) (hy' : IsFam m y') :
    IsFam m (fun c => y c + y' c) := by
  obtain ⟨r₀, Q, hQ, h⟩ := hy
  obtain ⟨r₀', Q', hQ', h'⟩ := hy'
  refine ⟨min r₀ r₀', fun r => Q r + Q' r, fun r hr => ?_, fun c => ⟨?_, fun r => ?_⟩⟩
  · change Q r + Q' r = 0
    rw [hQ r (lt_of_lt_of_le hr (min_le_left _ _)), hQ' r (lt_of_lt_of_le hr (min_le_right _ _)), add_zero]
  · exact (ratSubring m).add_mem (h c).1 (h' c).1
  · rw [cf_add, (h c).2 r, (h' c).2 r, map_add]

theorem isFam_zero (m : ℕ+) : IsFam m (fun _ : σ → ℂ => (0 : Ser)) :=
  isFam_const m 0 (ratSubring m).zero_mem

theorem isFam_sum {m : ℕ+} {ι : Type} (s : Finset ι) (y : ι → (σ → ℂ) → Ser)
    (hy : ∀ k ∈ s, IsFam m (y k)) : IsFam m (fun c => ∑ k ∈ s, y k c) := by
  induction s using Finset.induction_on with
  | empty => simpa using isFam_zero (σ := σ) m
  | insert a s ha ih =>
    have h1 := isFam_add (hy a (Finset.mem_insert_self a s))
      (ih fun k hk => hy k (Finset.mem_insert_of_mem hk))
    convert h1 using 2
    rw [Finset.sum_insert ha]

theorem cf_mul_mono (m : ℕ+) (y : Ser) (j : ℕ) (a : ℂ) (r : ℤ) :
    cf (y * mono m j a) (zlev m r) = cf y (zlev m (r - j)) * a := by
  have h : ((y * mono m j a : Ser) : HahnSeries ℚ ℂ) = (y : HahnSeries ℚ ℂ) * single (lev m j) a := by
    change (y : HahnSeries ℚ ℂ) * ((mono m j a : Ser) : HahnSeries ℚ ℂ) = _
    rw [mono_coe]
  rw [cf, h, ← zlev_sub m r j, coeff_mul_single_add]
  rfl

theorem isFam_mul_mono {m : ℕ+} {y : (σ → ℂ) → Ser} (hy : IsFam m y) (j : ℕ) (s : σ) :
    IsFam m (fun c => y c * mono m j (c s)) := by
  obtain ⟨r₀, Q, hQ, h⟩ := hy
  refine ⟨r₀, fun r => Q (r - j) * MvPolynomial.X s, fun r hr => ?_, fun c => ⟨?_, fun r => ?_⟩⟩
  · change Q (r - j) * MvPolynomial.X s = 0
    rw [hQ (r - j) (by omega), zero_mul]
  · exact (ratSubring m).mul_mem (h c).1 (mono_rational m j (c s))
  · rw [cf_mul_mono, (h c).2 (r - j), map_mul, MvPolynomial.eval_X]

/-- A point whose `i`-th coordinate is `Σ_{k < len i} c_{var i k} t^{lvl i k / m}`. -/
structure PolyPoint (σ : Type) (N : ℕ) where
  len : Fin N → ℕ
  lvl : Fin N → ℕ → ℕ
  var : Fin N → ℕ → σ

/-- The point of a `PolyPoint` at the parameter `c`. -/
def PolyPoint.eval {N : ℕ} (p : PolyPoint σ N) (m : ℕ+) (c : σ → ℂ) : Fin N → Ser :=
  fun i => ∑ k ∈ Finset.range (p.len i), mono m (p.lvl i k) (c (p.var i k))

/-- A polynomial over `ℂ((t^{1/m}))` at a polynomial point is a family with polynomial
coefficients. -/
theorem fam_poly {N : ℕ} (m : ℕ+) (p : PolyPoint σ N) (P : MvPolynomial (Fin N) (ratSubring m)) :
    IsFam m (fun c => MvPolynomial.eval₂ (ratSubring m).subtype (p.eval m c) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    exact isFam_const m a.val a.property
  | add P Q hP hQ =>
    simp only [MvPolynomial.eval₂_add]
    exact isFam_add hP hQ
  | mul_X P i hP =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, PolyPoint.eval, Finset.mul_sum]
    exact isFam_sum _ _ fun k _ => isFam_mul_mono hP (p.lvl i k) (p.var i k)

/-! ### The Noetherian bound -/

/-- If the polynomials `Q r`, `r ≤ R`, vanish at `c` then all `Q r` vanish at `c`, for a bound `R`
that does not depend on `c`. -/
theorem exists_bound [Finite σ] (Q : ℤ → MvPolynomial σ ℂ) :
    ∃ R : ℤ, ∀ c : σ → ℂ, (∀ r, r ≤ R → MvPolynomial.eval c (Q r) = 0) →
      ∀ r, MvPolynomial.eval c (Q r) = 0 := by
  have hfg : (Ideal.span (Set.range Q)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range Q)).mp hfg
  have hidx : ∀ q ∈ s, ∃ r : ℤ, Q r = q := fun q hq => hs hq
  choose! idx hidx using hidx
  obtain ⟨R, hR⟩ := (s.image idx).exists_le
  refine ⟨R, fun c hc r => ?_⟩
  have hker : Ideal.span (Set.range Q) ≤ RingHom.ker (MvPolynomial.eval c) := by
    change Submodule.span _ (Set.range Q) ≤ _
    rw [hspan]
    refine Submodule.span_le.mpr fun q hq => ?_
    rw [SetLike.mem_coe, RingHom.mem_ker, ← hidx q hq]
    exact hc _ (hR _ (Finset.mem_image_of_mem idx hq))
  exact hker (Ideal.subset_span ⟨r, rfl⟩)

/-! ### `rv` of a rational series -/

theorem eq_zero_of_cf {m : ℕ+} {y : Ser} (hy : IsRational m y) (h : ∀ r : ℤ, cf y (zlev m r) = 0) :
    y = 0 := by
  apply Subtype.ext
  ext γ
  by_contra hne
  obtain ⟨z, rfl⟩ := hy γ hne
  exact hne (h z)

theorem rvOfField_zero' : rvOfField (0 : Ser) = none := by
  simp [rvOfField, RVCalc.rv_zero, rvNormalEquiv, _root_.Equiv.optionCongr]

/-- `rv` of an `m`-rational series whose first nonzero coefficient is at level `r/m`. -/
theorem rvOfField_eq_linePoint {m : ℕ+} {y : Ser} (hy : IsRational m y) (r : ℤ)
    (hr : cf y (zlev m r) ≠ 0) (hlow : ∀ r' : ℤ, r' < r → cf y (zlev m r') = 0) :
    rvOfField y = linePoint (zlev m r) (cf y (zlev m r)) := by
  have hy0 : y ≠ 0 := fun h => hr (by rw [h]; rfl)
  have hy' : (y : HahnSeries ℚ ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hord : (y : HahnSeries ℚ ℂ).order = zlev m r := by
    obtain ⟨z, hz⟩ := hy (y : HahnSeries ℚ ℂ).order (coeff_order_ne hy')
    have hz' : (y : HahnSeries ℚ ℂ).order = zlev m z := hz
    have h1 : zlev m z ≤ zlev m r := hz' ▸ order_le_of_coeff_ne_zero hr
    have h2 : ¬ z < r := fun hlt => by
      have := hlow z hlt
      rw [← hz'] at this
      exact coeff_order_ne hy' this
    have h3 : z = r := by
      rcases lt_trichotomy z r with h | h | h
      · exact absurd h h2
      · exact h
      · exact absurd h1 (not_le.mpr (zlev_lt h))
    rw [hz', h3]
  rw [rvOfField, RVCalc.rv_of_ne hy0]
  change some (puiseuxRVUnitEquiv (QuotientGroup.mk' _ (Units.mk0 y hy0))) = _
  rw [puiseuxRVUnitEquiv_mk, linePoint, dif_neg hr]
  congr 1
  refine Prod.ext ?_ (Units.ext ?_)
  · change Multiplicative.ofAdd (y : HahnSeries ℚ ℂ).order = _
    rw [hord]
  · change (y : HahnSeries ℚ ℂ).leadingCoeff = cf y (zlev m r)
    rw [leadingCoeff_eq, hord]
    rfl

end DiamondIntegral.Section8.Truncation
