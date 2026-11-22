import FubiniTheorems.Comparison.PuiseuxModels.PuiseuxRVLanguage

/-! Truncations of points rational over `ℂ((t^{1/m}))` in the concrete Puiseux model, and the
set-theoretic form of Lemma 8.5.

In the concrete model the field sort is `ℂ{{t}}` (Puiseux series, a subfield of the Hahn series
`ℂ((t^ℚ))`) and `RV = Option (ℚ × ℂˣ)`, where `(γ, c)` is `rv(c t^γ)` and `none` is `rv(0)`.

* `IsRational m x`: `x ∈ ℂ((t^{1/m}))`, i.e. the support of `x` is in `m⁻¹ℤ`; `IsIntegral x`: `x ∈ 𝒪`.
* `coeffRV γ c = rv(c t^γ)`, an element of the residue line `Line γ = γ^♯ ∪ {0}`.
* `truncPoint m b x`: for cutoffs `β_i = b_i / m`, the tuple of the coefficients of `t^{j/m}`,
  `0 ≤ j ≤ b_i`, of `x_i`, each regarded as an element of `Line (j/m)`.
* `truncSet m b A`: the truncation `A[m;β]` of a set `A ⊆ 𝒪^n × RV^l` of concrete points: the tuples
  `(truncPoint m b x, u)` for `(x, u) ∈ A` with `x` rational and integral and `u` rational.
* `lemma_8_5_sets`: if `A` is `β`-invariant and `β ≤ β'`, then `A[m;β']` is the set of tuples whose
  restriction to the indices `≤ β` lies in `A[m;β]` and whose other entries lie on their residue
  lines: `A[m;β'] = A[m;β] × ∏_i ∏_{β_i < γ ≤ β'_i} L_γ` (manuscript, proof of Lemma 8.5). -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical HahnSeries
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal

/-- The field sort of the concrete model. -/
abbrev Ser := Section5.PuiseuxSeries ℂ

/-- The coefficient of `t^γ`. -/
def cf (x : Ser) (γ : ℚ) : ℂ := (x : HahnSeries ℚ ℂ).coeff γ

/-- The coefficient of `t^γ`, as an additive map. -/
def cfHom (γ : ℚ) : Ser →+ ℂ where
  toFun x := cf x γ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cfHom_apply (γ : ℚ) (x : Ser) : cfHom γ x = cf x γ := rfl

theorem cf_add (x y : Ser) (γ : ℚ) : cf (x + y) γ = cf x γ + cf y γ := rfl

theorem cf_sum {ι : Type*} (s : Finset ι) (f : ι → Ser) (γ : ℚ) :
    cf (∑ j ∈ s, f j) γ = ∑ j ∈ s, cf (f j) γ := by
  rw [← cfHom_apply, map_sum]
  rfl

/-- The level `j/m`. -/
def lev (m : ℕ+) (j : ℕ) : ℚ := (j : ℚ) / ((m : ℕ) : ℚ)

theorem lev_nonneg (m : ℕ+) (j : ℕ) : 0 ≤ lev m j :=
  div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg _)

theorem lev_lt_lev {m : ℕ+} {j k : ℕ} (h : j < k) : lev m j < lev m k := by
  have hm : (0 : ℚ) < ((m : ℕ) : ℚ) := by exact_mod_cast m.pos
  exact div_lt_div_of_pos_right (by exact_mod_cast h) hm

theorem lev_injective (m : ℕ+) : Function.Injective (lev m) := by
  intro j k h
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exact absurd h (lev_lt_lev hjk).ne
  · exact hjk
  · exact absurd h.symm (lev_lt_lev hjk).ne

/-- The monomial `c t^{j/m}`. -/
def mono (m : ℕ+) (j : ℕ) (c : ℂ) : Ser := puiseuxConstant c * puiseuxRoot m ^ j

theorem mono_coe (m : ℕ+) (j : ℕ) (c : ℂ) :
    ((mono m j c : Ser) : HahnSeries ℚ ℂ) = single (lev m j) c := by
  change (puiseuxConstant c : HahnSeries ℚ ℂ) * (puiseuxRoot (k := ℂ) m : HahnSeries ℚ ℂ) ^ j = _
  rw [puiseuxConstant_coe, puiseuxRoot_coe, single_pow, one_pow, C_apply, single_mul_single, zero_add,
    mul_one]
  congr 1
  rw [nsmul_eq_mul, lev, mul_one_div]

theorem cf_mono (m : ℕ+) (j : ℕ) (c : ℂ) (γ : ℚ) : cf (mono m j c) γ = if γ = lev m j then c else 0 := by
  rw [cf, mono_coe, coeff_single]
  split_ifs <;> rfl

/-- `x ∈ ℂ((t^{1/m}))`. -/
def IsRational (m : ℕ+) (x : Ser) : Prop := ∀ γ : ℚ, cf x γ ≠ 0 → ∃ z : ℤ, γ = (z : ℚ) / ((m : ℕ) : ℚ)

/-- `x ∈ 𝒪`. -/
def IsIntegral (x : Ser) : Prop := ∀ γ : ℚ, γ < 0 → cf x γ = 0

/-- `rv(c t^γ)`. -/
def coeffRV (γ : ℚ) (c : ℂ) : RV := if h : c = 0 then none else some (Multiplicative.ofAdd γ, Units.mk0 c h)

/-- The coefficient of an element of a residue line. -/
def lineCoeff : RV → ℂ
  | none => 0
  | some u => (u.2 : ℂ)

/-- The residue line `L_γ = γ^♯ ∪ {0}`. -/
def Line (γ : ℚ) : Set RV := {r | r = none ∨ ∃ c : ℂˣ, r = some (Multiplicative.ofAdd γ, c)}

theorem lineCoeff_coeffRV (γ : ℚ) (c : ℂ) : lineCoeff (coeffRV γ c) = c := by
  unfold coeffRV
  split_ifs with h
  · exact h.symm
  · rfl

theorem coeffRV_mem_line (γ : ℚ) (c : ℂ) : coeffRV γ c ∈ Line γ := by
  unfold coeffRV
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem coeffRV_lineCoeff {γ : ℚ} {r : RV} (hr : r ∈ Line γ) : coeffRV γ (lineCoeff r) = r := by
  rcases hr with rfl | ⟨c, rfl⟩
  · simp [coeffRV, lineCoeff]
  · have hc : (c : ℂ) ≠ 0 := c.ne_zero
    simp only [coeffRV, lineCoeff, hc, ↓reduceDIte]
    congr 2
    exact Units.ext rfl

/-- An RV element of `ℂ((t^{1/m}))`: `rv(0)`, or `rv(c t^γ)` with `γ ∈ m⁻¹ℤ`. -/
def LabelRational (m : ℕ+) (r : RV) : Prop :=
  ∀ u, r = some u → ∃ z : ℤ, Multiplicative.toAdd u.1 = (z : ℚ) / ((m : ℕ) : ℚ)

variable {n l : ℕ}

/-- The indices of the truncated coefficients: `(i, j)` with `0 ≤ j ≤ b_i`. -/
abbrev Idx (b : Fin n → ℕ) := Σ i : Fin n, Fin (b i + 1)

/-- The truncation of a tuple at the cutoffs `β_i = b_i / m`. -/
def truncPoint (m : ℕ+) (b : Fin n → ℕ) (x : Fin n → Ser) : Idx b → RV :=
  fun k => coeffRV (lev m k.2) (cf (x k.1) (lev m k.2))

/-- **The truncation `A[m;β]`.** -/
def truncSet (m : ℕ+) (b : Fin n → ℕ) (A : Set ((Fin n → Ser) × (Fin l → RV))) :
    Set (Idx b ⊕ Fin l → RV) :=
  {w | ∃ p ∈ A, (∀ i, IsRational m (p.1 i) ∧ IsIntegral (p.1 i)) ∧ (∀ j, LabelRational m (p.2 j)) ∧
    w = Sum.elim (truncPoint m b p.1) p.2}

/-- Congruence modulo `𝔪_β`. -/
def Congr (m : ℕ+) (b : Fin n → ℕ) (x x' : Fin n → Ser) : Prop :=
  ∀ i, ∀ γ : ℚ, γ ≤ lev m (b i) → cf (x i) γ = cf (x' i) γ

/-- `β`-invariance of a set of concrete points. -/
def Invariant (m : ℕ+) (b : Fin n → ℕ) (A : Set ((Fin n → Ser) × (Fin l → RV))) : Prop :=
  ∀ x x' u, (x, u) ∈ A → Congr m b x x' → (x', u) ∈ A

variable {b b' : Fin n → ℕ}

/-- The inclusion of the indices `≤ β` into the indices `≤ β'`. -/
def restrictIdx (h : ∀ i, b i ≤ b' i) : Idx b → Idx b' :=
  fun k => ⟨k.1, Fin.castLE (Nat.succ_le_succ (h k.1)) k.2⟩

/-- Restriction of a truncated tuple to the indices `≤ β`. -/
def restrict (h : ∀ i, b i ≤ b' i) (w : Idx b' ⊕ Fin l → RV) : Idx b ⊕ Fin l → RV :=
  w ∘ Sum.map (restrictIdx h) id

/-- The point with the coefficients of `x` up to `β` and prescribed coefficients between `β` and
`β'`. -/
def extend (m : ℕ+) (b b' : Fin n → ℕ) (x : Fin n → Ser) (w : Idx b' → RV) : Fin n → Ser :=
  fun i => x i + ∑ j : Fin (b' i + 1), if b i < (j : ℕ) then
    mono m j (lineCoeff (w ⟨i, j⟩) - cf (x i) (lev m j)) else 0

theorem cf_extend (m : ℕ+) (x : Fin n → Ser) (w : Idx b' → RV) (i : Fin n) (γ : ℚ) :
    cf (extend m b b' x w i) γ = cf (x i) γ + ∑ j : Fin (b' i + 1),
      if b i < (j : ℕ) ∧ γ = lev m j then lineCoeff (w ⟨i, j⟩) - cf (x i) (lev m j) else 0 := by
  rw [extend, cf_add, cf_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : b i < (j : ℕ)
  · simp only [hj, ite_true, true_and, cf_mono]
  · simp only [hj, ite_false, false_and]
    rfl

theorem cf_extend_level (m : ℕ+) (x : Fin n → Ser) (w : Idx b' → RV) (i : Fin n) (j : Fin (b' i + 1)) :
    cf (extend m b b' x w i) (lev m j) =
      if b i < (j : ℕ) then lineCoeff (w ⟨i, j⟩) else cf (x i) (lev m j) := by
  rw [cf_extend, Finset.sum_eq_single j]
  · by_cases hj : b i < (j : ℕ)
    · simp only [hj, true_and, ite_true]
      ring
    · simp only [hj, false_and, ite_false, add_zero]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hk (Fin.ext (lev_injective m h)).symm
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem cf_extend_of_not_level (m : ℕ+) (x : Fin n → Ser) (w : Idx b' → RV) (i : Fin n) (γ : ℚ)
    (hγ : ∀ j : Fin (b' i + 1), b i < (j : ℕ) → γ ≠ lev m j) :
    cf (extend m b b' x w i) γ = cf (x i) γ := by
  rw [cf_extend, Finset.sum_eq_zero, add_zero]
  intro j _
  rw [if_neg]
  rintro ⟨hj, h⟩
  exact hγ j hj h

/-- **Lemma 8.5, set-theoretic form.** For a `β`-invariant set `A` and `β ≤ β'`,
`A[m;β'] = A[m;β] × ∏_i ∏_{β_i < γ ≤ β'_i} L_γ`. -/
theorem lemma_8_5_sets (m : ℕ+) (h : ∀ i, b i ≤ b' i) (A : Set ((Fin n → Ser) × (Fin l → RV)))
    (hA : Invariant m b A) :
    truncSet m b' A = {w | restrict h w ∈ truncSet m b A ∧ ∀ k : Idx b', w (.inl k) ∈ Line (lev m k.2)} := by
  ext w
  constructor
  · rintro ⟨p, hp, hr, hu, rfl⟩
    refine ⟨⟨p, hp, hr, hu, ?_⟩, fun k => coeffRV_mem_line _ _⟩
    funext k
    cases k with
    | inl k => rfl
    | inr j => rfl
  · rintro ⟨⟨p, hp, hr, hu, hw⟩, hline⟩
    have hw1 : ∀ k : Idx b, w (.inl (restrictIdx h k)) = truncPoint m b p.1 k := fun k =>
      congrFun hw (.inl k)
    have hw2 : ∀ j : Fin l, w (.inr j) = p.2 j := fun j => congrFun hw (.inr j)
    let x' := extend m b b' p.1 (fun k => w (.inl k))
    have hcongr : Congr m b p.1 x' := by
      intro i γ hγ
      symm
      apply cf_extend_of_not_level
      intro j hj hγj
      rw [hγj] at hγ
      exact absurd hγ (not_le.mpr (lev_lt_lev hj))
    refine ⟨(x', p.2), hA p.1 x' p.2 hp hcongr, fun i => ⟨?_, ?_⟩, hu, ?_⟩
    · intro γ hγ
      by_cases hlev : ∃ j : Fin (b' i + 1), b i < (j : ℕ) ∧ γ = lev m j
      · obtain ⟨j, -, rfl⟩ := hlev
        exact ⟨(j : ℕ), by rw [lev]; push_cast; rfl⟩
      · push Not at hlev
        rw [cf_extend_of_not_level m p.1 _ i γ hlev] at hγ
        exact (hr i).1 γ hγ
    · intro γ hγ
      rw [cf_extend_of_not_level m p.1 _ i γ]
      · exact (hr i).2 γ hγ
      · intro j _ hγj
        rw [hγj] at hγ
        exact absurd (lev_nonneg m j) (not_le.mpr hγ)
    · funext k
      cases k with
      | inr j => exact hw2 j
      | inl k =>
        obtain ⟨i, j⟩ := k
        change w (.inl ⟨i, j⟩) = coeffRV (lev m j) (cf (x' i) (lev m j))
        rw [cf_extend_level]
        by_cases hj : b i < (j : ℕ)
        · rw [if_pos hj]
          exact (coeffRV_lineCoeff (hline ⟨i, j⟩)).symm
        · rw [if_neg hj]
          have hj' : (j : ℕ) < b i + 1 := Nat.lt_succ_of_le (not_lt.mp hj)
          have := hw1 ⟨i, ⟨(j : ℕ), hj'⟩⟩
          have hidx : restrictIdx h ⟨i, ⟨(j : ℕ), hj'⟩⟩ = ⟨i, j⟩ := by
            simp only [restrictIdx]
            congr 1
          rw [hidx] at this
          exact this

end DiamondIntegral.Section8.Truncation
