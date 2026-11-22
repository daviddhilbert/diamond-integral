import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Chains of height functions over a simplex.

A function that is affine on a simplex with vertices indexed by `ι` is given by
its values `u : ι → ℚ` at the vertices; at the point with barycentric
coordinates `t` its value is `ev t u = ∑ t_i u_i`. This file contains the
order-theoretic part of the prism decomposition (Step 1 of the direct proof of
Hrushovski–Loeser, Lemma 8.5.2):

* functions of constant sign on the open simplex are comparable at the vertices;
* a finite chain of height functions cuts the cylinder over the simplex into
  graphs and bands between consecutive members, without overlaps;
* every finite chain can be refined to one whose consecutive members differ at
  exactly one vertex (the band between such a pair is a simplex).

The file uses Mathlib only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.HeightChains

variable {ι : Type*} [Fintype ι]

/-- The value at barycentric coordinates `t` of the affine function with vertex values `u`. -/
def ev (t u : ι → ℚ) : ℚ := ∑ i, t i * u i

/-- Barycentric coordinates of a point of the open simplex. -/
def IsBary (t : ι → ℚ) : Prop := (∀ i, 0 < t i) ∧ ∑ i, t i = 1

theorem ev_sub (t u u' : ι → ℚ) : ev t (u - u') = ev t u - ev t u' := by
  simp [ev, mul_sub, Finset.sum_sub_distrib]

theorem ev_const {t : ι → ℚ} (ht : IsBary t) (c : ℚ) : ev t (fun _ => c) = c := by
  simp [ev, ← Finset.sum_mul, ht.2]

theorem ev_mono {t : ι → ℚ} (ht : IsBary t) {u u' : ι → ℚ} (h : u ≤ u') : ev t u ≤ ev t u' :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (ht.1 i).le

theorem ev_strictMono {t : ι → ℚ} (ht : IsBary t) {u u' : ι → ℚ} (h : u < u') :
    ev t u < ev t u' := by
  obtain ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (ht.1 i).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (ht.1 i)⟩

/-- The barycentre. -/
theorem isBary_barycentre [Nonempty ι] : IsBary (fun _ : ι => (1 : ℚ) / Fintype.card ι) := by
  have hc : (0 : ℚ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun _ => div_pos one_pos hc, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

section signs

variable [DecidableEq ι]

/-- The point `(1 − ε) b + ε e_i`. -/
theorem isBary_towards {b : ι → ℚ} (hb : IsBary b) (i₀ : ι) {ε : ℚ} (h0 : 0 < ε) (h1 : ε < 1) :
    IsBary (fun i => (1 - ε) * b i + ε * (if i = i₀ then 1 else 0)) := by
  refine ⟨fun i => ?_, ?_⟩
  · have h : 0 < (1 - ε) * b i := mul_pos (by linarith) (hb.1 i)
    have h' : 0 ≤ ε * (if i = i₀ then (1 : ℚ) else 0) := by
      split_ifs <;> simp [h0.le]
    linarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb.2]
    simp

theorem ev_towards (b u : ι → ℚ) (i₀ : ι) (ε : ℚ) :
    ev (fun i => (1 - ε) * b i + ε * (if i = i₀ then 1 else 0)) u =
      (1 - ε) * ev b u + ε * u i₀ := by
  simp [ev, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- A function that is positive on the open simplex is nonnegative at the vertices. -/
theorem nonneg_of_pos [Nonempty ι] {u : ι → ℚ} (h : ∀ t, IsBary t → 0 < ev t u) : 0 ≤ u := by
  intro i₀
  by_contra hneg
  have ha : u i₀ < 0 := lt_of_not_ge hneg
  have hb := isBary_barycentre (ι := ι)
  set b : ι → ℚ := fun _ => (1 : ℚ) / Fintype.card ι
  have hgb : 0 < ev b u := h b hb
  have hden : 0 < ev b u - u i₀ := by linarith
  set ε : ℚ := ev b u / (ev b u - u i₀)
  have h0 : 0 < ε := div_pos hgb hden
  have h1 : ε < 1 := (div_lt_one hden).mpr (by linarith)
  have hz := h _ (isBary_towards hb i₀ h0 h1)
  rw [ev_towards] at hz
  have he : (1 - ε) * ev b u + ε * u i₀ = 0 := by
    simp only [ε]
    field_simp
    ring
  linarith

/-- A function that vanishes on the open simplex vanishes at the vertices. -/
theorem eq_zero_of_zero [Nonempty ι] {u : ι → ℚ} (h : ∀ t, IsBary t → ev t u = 0) : u = 0 := by
  funext i₀
  have hb := isBary_barycentre (ι := ι)
  have h1 := h _ hb
  have h2 := h _ (isBary_towards hb i₀ (ε := 1 / 2) (by norm_num) (by norm_num))
  rw [ev_towards, h1] at h2
  simp only [Pi.zero_apply]
  linarith

/-- Two functions whose difference has constant sign on the open simplex are comparable at
the vertices. -/
theorem comparable_of_sign [Nonempty ι] {u u' : ι → ℚ}
    (h : (∀ t, IsBary t → ev t u < ev t u') ∨ (∀ t, IsBary t → ev t u = ev t u') ∨
      (∀ t, IsBary t → ev t u' < ev t u)) : u ≤ u' ∨ u' ≤ u := by
  rcases h with h | h | h
  · left
    have := nonneg_of_pos (u := u' - u) fun t ht => by rw [ev_sub]; linarith [h t ht]
    exact fun i => by have := this i; simp only [Pi.zero_apply, Pi.sub_apply] at this; linarith
  · left
    have := eq_zero_of_zero (u := u' - u) fun t ht => by rw [ev_sub]; linarith [h t ht]
    exact fun i => by
      have := congrFun this i; simp only [Pi.zero_apply, Pi.sub_apply] at this; linarith
  · right
    have := nonneg_of_pos (u := u - u') fun t ht => by rw [ev_sub]; linarith [h t ht]
    exact fun i => by have := this i; simp only [Pi.zero_apply, Pi.sub_apply] at this; linarith

end signs

/-! ### Chains -/

/-- A finite set of height functions that is totally ordered at the vertices. -/
def IsChainF (W : Finset (ι → ℚ)) : Prop := ∀ u ∈ W, ∀ u' ∈ W, u ≤ u' ∨ u' ≤ u

/-- Consecutive members of `W`. -/
def Consec (W : Finset (ι → ℚ)) (f g : ι → ℚ) : Prop :=
  f ∈ W ∧ g ∈ W ∧ f < g ∧ ∀ w ∈ W, ¬(f < w ∧ w < g)

/-- Consecutive members differ at one vertex only. -/
def Elementary (W : Finset (ι → ℚ)) : Prop :=
  ∀ f g, Consec W f g → ∃ j, ∀ i, i ≠ j → f i = g i

theorem lt_of_ev_lt {W : Finset (ι → ℚ)} (hW : IsChainF W) {t : ι → ℚ} (ht : IsBary t)
    {u u' : ι → ℚ} (hu : u ∈ W) (hu' : u' ∈ W) (h : ev t u < ev t u') : u < u' := by
  rcases hW u hu u' hu' with h1 | h1
  · exact lt_of_le_of_ne h1 fun he => by rw [he] at h; exact lt_irrefl _ h
  · exact absurd (ev_mono ht h1) (not_le.mpr h)

/-- Two members of a chain with the same value at a point are equal. -/
theorem eq_of_ev_eq {W : Finset (ι → ℚ)} (hW : IsChainF W) {t : ι → ℚ} (ht : IsBary t)
    {u u' : ι → ℚ} (hu : u ∈ W) (hu' : u' ∈ W) (h : ev t u = ev t u') : u = u' := by
  rcases hW u hu u' hu' with h1 | h1
  · by_contra hne
    exact absurd h (ev_strictMono ht (lt_of_le_of_ne h1 hne)).ne
  · by_contra hne
    exact absurd h.symm (ev_strictMono ht (lt_of_le_of_ne h1 (Ne.symm hne))).ne

/-- A point of the cylinder lies on a graph or in a band between consecutive members. -/
theorem graph_or_band {W : Finset (ι → ℚ)} (hW : IsChainF W) {t : ι → ℚ} (ht : IsBary t)
    {y : ℚ} (hlo : ∃ l ∈ W, ev t l ≤ y) (hhi : ∃ h ∈ W, y ≤ ev t h) :
    (∃ w ∈ W, ev t w = y) ∨ ∃ f g, Consec W f g ∧ ev t f < y ∧ y < ev t g := by
  classical
  by_cases hex : ∃ w ∈ W, ev t w = y
  · exact Or.inl hex
  right
  have hne : ∀ w ∈ W, ev t w ≠ y := fun w hw he => hex ⟨w, hw, he⟩
  obtain ⟨l, hl, hly⟩ := hlo
  obtain ⟨h, hh, hyh⟩ := hhi
  have hl' : l ∈ W.filter fun w => ev t w < y :=
    Finset.mem_filter.mpr ⟨hl, lt_of_le_of_ne hly (hne l hl)⟩
  have hh' : h ∈ W.filter fun w => y < ev t w :=
    Finset.mem_filter.mpr ⟨hh, lt_of_le_of_ne hyh (Ne.symm (hne h hh))⟩
  obtain ⟨f, hf, hfmax⟩ := Finset.exists_max_image _ (ev t) ⟨l, hl'⟩
  obtain ⟨g, hg, hgmin⟩ := Finset.exists_min_image _ (ev t) ⟨h, hh'⟩
  rw [Finset.mem_filter] at hf hg
  refine ⟨f, g, ⟨hf.1, hg.1, lt_of_ev_lt hW ht hf.1 hg.1 (hf.2.trans hg.2), ?_⟩, hf.2, hg.2⟩
  rintro w hw ⟨hfw, hwg⟩
  rcases lt_or_gt_of_ne (hne w hw) with hlt | hgt
  · exact absurd (hfmax w (Finset.mem_filter.mpr ⟨hw, hlt⟩)) (not_le.mpr (ev_strictMono ht hfw))
  · exact absurd (hgmin w (Finset.mem_filter.mpr ⟨hw, hgt⟩)) (not_le.mpr (ev_strictMono ht hwg))

/-- A graph does not meet a band between consecutive members. -/
theorem not_graph_and_band {W : Finset (ι → ℚ)} (hW : IsChainF W) {t : ι → ℚ} (ht : IsBary t)
    {w f g : ι → ℚ} (hw : w ∈ W) (hc : Consec W f g) (h1 : ev t f < ev t w)
    (h2 : ev t w < ev t g) : False :=
  hc.2.2.2 w hw ⟨lt_of_ev_lt hW ht hc.1 hw h1, lt_of_ev_lt hW ht hw hc.2.1 h2⟩

/-- Two bands between consecutive members that share a point are the same band. -/
theorem band_unique {W : Finset (ι → ℚ)} (hW : IsChainF W) {t : ι → ℚ} (ht : IsBary t) {y : ℚ}
    {f g f' g' : ι → ℚ} (hc : Consec W f g) (hc' : Consec W f' g') (h1 : ev t f < y)
    (h2 : y < ev t g) (h1' : ev t f' < y) (h2' : y < ev t g') : f = f' ∧ g = g' := by
  have key : ∀ {f g f' g' : ι → ℚ}, Consec W f g → Consec W f' g' → ev t f < y → y < ev t g →
      ev t f' < y → y < ev t g' → ¬ ev t f < ev t f' := by
    intro f g f' g' hc hc' h1 h2 h1' h2' hlt
    exact not_graph_and_band hW ht hc'.1 hc hlt (h1'.trans h2)
  have key' : ∀ {f g f' g' : ι → ℚ}, Consec W f g → Consec W f' g' → ev t f < y → y < ev t g →
      ev t f' < y → y < ev t g' → ¬ ev t g < ev t g' := by
    intro f g f' g' hc hc' h1 h2 h1' h2' hlt
    exact not_graph_and_band hW ht hc.2.1 hc' (h1'.trans h2) hlt
  have hf : ev t f = ev t f' :=
    le_antisymm (not_lt.mp (key hc' hc h1' h2' h1 h2)) (not_lt.mp (key hc hc' h1 h2 h1' h2'))
  have hg : ev t g = ev t g' :=
    le_antisymm (not_lt.mp (key' hc' hc h1' h2' h1 h2)) (not_lt.mp (key' hc hc' h1 h2 h1' h2'))
  exact ⟨eq_of_ev_eq hW ht hc.1 hc'.1 hf, eq_of_ev_eq hW ht hc.2.1 hc'.2.1 hg⟩

/-- Every finite chain has an elementary refinement between the same bounds. -/
theorem exists_elementary_refinement [DecidableEq ι] (V : Finset (ι → ℚ)) (hV : IsChainF V) :
    ∃ W : Finset (ι → ℚ), V ⊆ W ∧ IsChainF W ∧ Elementary W ∧
      ∀ w ∈ W, ∃ f ∈ V, ∃ g ∈ V, f ≤ w ∧ w ≤ g := by
  classical
  let Grid : Finset (ι → ℚ) := Fintype.piFinset fun i => V.image fun u => u i
  have hVG : V ⊆ Grid := fun u hu =>
    Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem (fun u : ι → ℚ => u i) hu
  suffices H : ∀ m : ℕ, ∀ W : Finset (ι → ℚ), (Grid \ W).card = m → V ⊆ W → W ⊆ Grid →
      IsChainF W → (∀ w ∈ W, ∃ f ∈ V, ∃ g ∈ V, f ≤ w ∧ w ≤ g) →
      ∃ W' : Finset (ι → ℚ), V ⊆ W' ∧ IsChainF W' ∧ Elementary W' ∧
        ∀ w ∈ W', ∃ f ∈ V, ∃ g ∈ V, f ≤ w ∧ w ≤ g from
    H _ V rfl subset_rfl hVG hV fun w hw => ⟨w, hw, w, hw, le_rfl, le_rfl⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W hm hVW hWG hW hb
    by_cases hE : Elementary W
    · exact ⟨W, hVW, hW, hE, hb⟩
    · simp only [Elementary, not_forall] at hE
      obtain ⟨f, g, hc, hne⟩ := hE
      push Not at hne
      obtain ⟨hf, hg, hfg, hno⟩ := hc
      obtain ⟨hfgle, j₀, hj₀⟩ := Pi.lt_def.mp hfg
      let h : ι → ℚ := Function.update f j₀ (g j₀)
      have hfh : f < h := by
        refine Pi.lt_def.mpr ⟨fun i => ?_, j₀, by simp [h, hj₀]⟩
        by_cases hi : i = j₀
        · subst hi; simp [h, hj₀.le]
        · simp [h, hi]
      have hhg_le : h ≤ g := fun i => by
        by_cases hi : i = j₀
        · subst hi; simp [h]
        · simp [h, hi, hfgle i]
      have hhg : h < g := by
        obtain ⟨i, hi, hfi⟩ := hne j₀
        refine lt_of_le_of_ne hhg_le fun he => hfi ?_
        have := congrFun he i
        simpa [h, hi] using this
      have hhW : h ∉ W := fun hh => hno h hh ⟨hfh, hhg⟩
      have hhG : h ∈ Grid := by
        refine Fintype.mem_piFinset.mpr fun i => ?_
        by_cases hi : i = j₀
        · subst hi
          have := Fintype.mem_piFinset.mp (hWG hg) i
          simpa [h] using this
        · have := Fintype.mem_piFinset.mp (hWG hf) i
          simpa [h, hi] using this
      have hcmp : ∀ w ∈ W, w ≤ h ∨ h ≤ w := by
        intro w hw
        rcases hW w hw f hf with h1 | h1
        · exact Or.inl (h1.trans hfh.le)
        · rcases eq_or_lt_of_le h1 with h2 | h2
          · exact Or.inl (by rw [← h2]; exact hfh.le)
          · rcases hW w hw g hg with h3 | h3
            · rcases eq_or_lt_of_le h3 with h4 | h4
              · exact Or.inr (by rw [h4]; exact hhg.le)
              · exact absurd ⟨h2, h4⟩ (hno w hw)
            · exact Or.inr (hhg.le.trans h3)
      have hchain : IsChainF (insert h W) := by
        intro u hu u' hu'
        rcases Finset.mem_insert.mp hu with hu | hu <;>
          rcases Finset.mem_insert.mp hu' with hu' | hu'
        · rw [hu, hu']; exact Or.inl le_rfl
        · rw [hu]; exact (hcmp u' hu').symm
        · rw [hu']; exact hcmp u hu
        · exact hW u hu u' hu'
      have hsub : insert h W ⊆ Grid := Finset.insert_subset hhG hWG
      have hcard : (Grid \ insert h W).card < m := by
        rw [← hm, Finset.sdiff_insert]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hhG, hhW⟩)
      have hb' : ∀ w ∈ insert h W, ∃ f ∈ V, ∃ g ∈ V, f ≤ w ∧ w ≤ g := by
        intro w hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · obtain ⟨f₁, hf₁, -, -, h1, -⟩ := hb f hf
          obtain ⟨-, -, g₂, hg₂, -, h2⟩ := hb g hg
          rw [hw]
          exact ⟨f₁, hf₁, g₂, hg₂, h1.trans hfh.le, hhg.le.trans h2⟩
        · exact hb w hw
      exact ih _ hcard (insert h W) rfl (hVW.trans (Finset.subset_insert _ _)) hsub hchain hb'

end DiamondIntegral.Section8.HeightChains
