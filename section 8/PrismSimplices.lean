import «section 8».SimplexSeries
import «section 8».HeightChains
import Mathlib.Algebra.BigOperators.Fin

/-! Graphs and bands over a simplex (the prism lemma).

Over an open simplex with affinely independent vertices `v i ∈ ℚⁿ`, a height
function `u` (given by its values at the vertices) has a graph in `ℚⁿ⁺¹`, which
is the open simplex on the lifted vertices `(v i, u i)`. The band between two
height functions that differ at one vertex `j` only is the open simplex with
the additional vertex `(v j, g j)`. A chain of height functions cuts the
cylinder into such graphs and bands without overlaps. The file uses Mathlib
only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.Prism

open SimplexSeries HeightChains

variable {n : ℕ}

theorem mem_openSimplex_iff {ι : Type*} [Fintype ι] (w : ι → Fin n → ℚ) (x : Fin n → ℚ) :
    x ∈ openSimplex w ↔ ∃ t : ι → ℚ, IsBary t ∧ ∀ i, x i = ∑ j, t j * w j i := by
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    exact ⟨t, h1, h2, h3⟩

/-- A criterion for affine independence of a finite family in a vector space. -/
theorem affineIndependent_of_forall {ι : Type*} [Fintype ι] {m : ℕ} (p : ι → Fin m → ℚ)
    (h : ∀ w : ι → ℚ, ∑ i, w i = 0 → (∀ c, ∑ i, w i * p i c = 0) → ∀ i, w i = 0) :
    AffineIndependent ℚ p := by
  classical
  rw [affineIndependent_iff]
  intro s w hs hsum i hi
  have h' := h (fun i => if i ∈ s then w i else 0)
    (by rw [Finset.sum_ite_mem, Finset.univ_inter]; exact hs)
    (fun c => by
      have hc := congrFun hsum c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      exact hc) i
  simpa [hi] using h'

theorem forall_of_affineIndependent {ι : Type*} [Fintype ι] {m : ℕ} {p : ι → Fin m → ℚ}
    (hp : AffineIndependent ℚ p) (w : ι → ℚ) (h0 : ∑ i, w i = 0)
    (h1 : ∀ c, ∑ i, w i * p i c = 0) : ∀ i, w i = 0 := fun i =>
  affineIndependent_iff.mp hp Finset.univ w h0
    (by
      funext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact h1 c) i (Finset.mem_univ i)

section base

variable {ι : Type*} [Fintype ι] (v : ι → Fin n → ℚ)

/-- The lifted vertices `(v i, u i)`. -/
def lift (u : ι → ℚ) : ι → Fin (n + 1) → ℚ := fun i => Fin.snoc (v i) (u i)

/-- `z` lies over the point of the base simplex with barycentric coordinates `t`. -/
def OverBase (t : ι → ℚ) (z : Fin (n + 1) → ℚ) : Prop :=
  ∀ i : Fin n, z (Fin.castSucc i) = ∑ j, t j * v j i

/-- The open band between two height functions. -/
def band (f g : ι → ℚ) : Set (Fin (n + 1) → ℚ) :=
  {z | ∃ t, IsBary t ∧ OverBase v t z ∧ ev t f < z (Fin.last n) ∧ z (Fin.last n) < ev t g}

/-- The closed cylinder between two height functions. -/
def cyl (lo hi : ι → ℚ) : Set (Fin (n + 1) → ℚ) :=
  {z | ∃ t, IsBary t ∧ OverBase v t z ∧ ev t lo ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ ev t hi}

theorem mem_graph_iff (u : ι → ℚ) (z : Fin (n + 1) → ℚ) :
    z ∈ openSimplex (lift v u) ↔
      ∃ t, IsBary t ∧ OverBase v t z ∧ z (Fin.last n) = ev t u := by
  rw [mem_openSimplex_iff]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Fin.forall_fin_succ']
  simp [lift, OverBase, ev]

variable {v}

theorem bary_unique (hv : AffineIndependent ℚ v) {t t' : ι → ℚ} (ht : IsBary t)
    (ht' : IsBary t') {z : Fin (n + 1) → ℚ} (h : OverBase v t z) (h' : OverBase v t' z) :
    t = t' := by
  funext j
  have h0 := forall_of_affineIndependent hv (t - t')
    (by simp [Finset.sum_sub_distrib, ht.2, ht'.2])
    (fun c => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [← h c, ← h' c, sub_self]) j
  exact sub_eq_zero.mp h0

theorem indep_lift (hv : AffineIndependent ℚ v) (u : ι → ℚ) :
    AffineIndependent ℚ (lift v u) := by
  refine affineIndependent_of_forall _ fun w h0 h1 => ?_
  refine forall_of_affineIndependent hv w h0 fun c => ?_
  have := h1 (Fin.castSucc c)
  simpa [lift] using this

/-! ### The decomposition of the cylinder by a chain -/

variable {W : Finset (ι → ℚ)}

theorem cyl_cases (hW : IsChainF W) {lo hi : ι → ℚ} (hlo : lo ∈ W) (hhi : hi ∈ W)
    {z : Fin (n + 1) → ℚ} (hz : z ∈ cyl v lo hi) :
    (∃ w ∈ W, z ∈ openSimplex (lift v w)) ∨ ∃ f g, Consec W f g ∧ z ∈ band v f g := by
  obtain ⟨t, ht, hb, h1, h2⟩ := hz
  rcases graph_or_band hW ht ⟨lo, hlo, h1⟩ ⟨hi, hhi, h2⟩ with ⟨w, hw, he⟩ | ⟨f, g, hc, h3, h4⟩
  · exact Or.inl ⟨w, hw, (mem_graph_iff v w z).mpr ⟨t, ht, hb, he.symm⟩⟩
  · exact Or.inr ⟨f, g, hc, t, ht, hb, h3, h4⟩

theorem graph_subset_cyl {lo hi w : ι → ℚ} (h1 : lo ≤ w) (h2 : w ≤ hi) :
    openSimplex (lift v w) ⊆ cyl v lo hi := by
  intro z hz
  obtain ⟨t, ht, hb, he⟩ := (mem_graph_iff v w z).mp hz
  exact ⟨t, ht, hb, he ▸ ev_mono ht h1, he ▸ ev_mono ht h2⟩

theorem band_subset_cyl {lo hi f g : ι → ℚ} (h1 : lo ≤ f) (h2 : g ≤ hi) :
    band v f g ⊆ cyl v lo hi := by
  rintro z ⟨t, ht, hb, h3, h4⟩
  exact ⟨t, ht, hb, (ev_mono ht h1).trans h3.le, h4.le.trans (ev_mono ht h2)⟩

theorem graph_disjoint (hv : AffineIndependent ℚ v) (hW : IsChainF W) {w w' : ι → ℚ}
    (hw : w ∈ W) (hw' : w' ∈ W) (hne : w ≠ w') :
    Disjoint (openSimplex (lift v w)) (openSimplex (lift v w')) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨t, ht, hb, he⟩ := (mem_graph_iff v w z).mp hz
  obtain ⟨t', ht', hb', he'⟩ := (mem_graph_iff v w' z).mp hz'
  have htt := bary_unique hv ht ht' hb hb'
  subst htt
  exact hne (eq_of_ev_eq hW ht hw hw' (he.symm.trans he'))

theorem graph_band_disjoint (hv : AffineIndependent ℚ v) (hW : IsChainF W) {w f g : ι → ℚ}
    (hw : w ∈ W) (hc : Consec W f g) : Disjoint (openSimplex (lift v w)) (band v f g) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨t', ht', hb', h3, h4⟩
  obtain ⟨t, ht, hb, he⟩ := (mem_graph_iff v w z).mp hz
  have htt := bary_unique hv ht ht' hb hb'
  subst htt
  exact not_graph_and_band hW ht hw hc (he ▸ h3) (he ▸ h4)

theorem band_disjoint (hv : AffineIndependent ℚ v) (hW : IsChainF W) {f g f' g' : ι → ℚ}
    (hc : Consec W f g) (hc' : Consec W f' g') (hne : ¬(f = f' ∧ g = g')) :
    Disjoint (band v f g) (band v f' g') := by
  rw [Set.disjoint_left]
  rintro z ⟨t, ht, hb, h1, h2⟩ ⟨t', ht', hb', h1', h2'⟩
  have htt := bary_unique hv ht ht' hb hb'
  subst htt
  exact hne (band_unique hW ht hc hc' h1 h2 h1' h2')

/-- Every piece lies over the base simplex. -/
theorem graph_over_base {w : ι → ℚ} {z : Fin (n + 1) → ℚ} (hz : z ∈ openSimplex (lift v w)) :
    (fun i => z (Fin.castSucc i)) ∈ openSimplex v := by
  obtain ⟨t, ht, hb, -⟩ := (mem_graph_iff v w z).mp hz
  exact (mem_openSimplex_iff v _).mpr ⟨t, ht, hb⟩

theorem band_over_base {f g : ι → ℚ} {z : Fin (n + 1) → ℚ} (hz : z ∈ band v f g) :
    (fun i => z (Fin.castSucc i)) ∈ openSimplex v := by
  obtain ⟨t, ht, hb, -, -⟩ := hz
  exact (mem_openSimplex_iff v _).mpr ⟨t, ht, hb⟩

end base

/-! ### An elementary band is a simplex -/

section elementary

variable {k : ℕ} (v : Fin (k + 1) → Fin n → ℚ)

/-- The vertices of the band simplex: the lifted vertices `(v i, f i)` and `(v j, c)`. -/
def bandVertices (f : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (c : ℚ) :
    Fin (k + 2) → Fin (n + 1) → ℚ :=
  Fin.snoc (lift v f) (Fin.snoc (v j) c)

theorem ev_eq_of_eq_off {t f g : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    (hfg : ∀ i, i ≠ j → f i = g i) : ev t g = ev t f + t j * (g j - f j) := by
  have h : ev t (g - f) = t j * (g j - f j) := by
    unfold ev
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [hfg i hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [ev_sub] at h
  linarith

theorem mem_bandSimplex_iff (f : Fin (k + 1) → ℚ) (j : Fin (k + 1)) (c : ℚ)
    (z : Fin (n + 1) → ℚ) :
    z ∈ openSimplex (bandVertices v f j c) ↔
      ∃ s : Fin (k + 2) → ℚ, IsBary s ∧
        (∀ i : Fin n, z (Fin.castSucc i) =
          ∑ m : Fin (k + 1), s (Fin.castSucc m) * v m i + s (Fin.last (k + 1)) * v j i) ∧
        z (Fin.last n) = ∑ m : Fin (k + 1), s (Fin.castSucc m) * f m + s (Fin.last (k + 1)) * c := by
  rw [mem_openSimplex_iff]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Fin.forall_fin_succ']
  simp [bandVertices, lift, Fin.sum_univ_castSucc]

/-- The band between two height functions that differ at the vertex `j` only is an open
simplex. -/
theorem band_eq_simplex {f g : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    (hfg : ∀ i, i ≠ j → f i = g i) (hj : f j < g j) :
    band v f g = openSimplex (bandVertices v f j (g j)) := by
  have hd : 0 < g j - f j := sub_pos.mpr hj
  ext z
  rw [mem_bandSimplex_iff]
  constructor
  · rintro ⟨t, ht, hb, h1, h2⟩
    rw [ev_eq_of_eq_off hfg] at h2
    set c : ℚ := (z (Fin.last n) - ev t f) / (g j - f j) with hc
    have hcd : c * (g j - f j) = z (Fin.last n) - ev t f := div_mul_cancel₀ _ hd.ne'
    have hc0 : 0 < c := div_pos (sub_pos.mpr h1) hd
    have hc1 : c < t j := by
      rw [hc, div_lt_iff₀ hd]
      linarith
    refine ⟨Fin.snoc (fun i => t i - if i = j then c else 0) c, ⟨?_, ?_⟩, fun i => ?_, ?_⟩
    · rw [Fin.forall_fin_succ']
      refine ⟨fun i => ?_, by simpa using hc0⟩
      by_cases hi : i = j
      · subst hi
        simpa using hc1
      · simpa [hi] using ht.1 i
    · rw [Fin.sum_univ_castSucc]
      simp [Finset.sum_sub_distrib, ht.2]
    · rw [hb i]
      simp [sub_mul, Finset.sum_sub_distrib]
    · have he : ev t f = ∑ m, t m * f m := rfl
      simp only [Fin.snoc_castSucc, Fin.snoc_last, sub_mul, Finset.sum_sub_distrib, ite_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [← he]
      linarith
  · rintro ⟨s, hs, hb, hl⟩
    have hs0 := (Fin.forall_fin_succ'.mp hs.1)
    have hsum : ∑ m : Fin (k + 1), s (Fin.castSucc m) + s (Fin.last (k + 1)) = 1 := by
      rw [← Fin.sum_univ_castSucc]
      exact hs.2
    refine ⟨fun i => s (Fin.castSucc i) + if i = j then s (Fin.last (k + 1)) else 0, ⟨fun i => ?_, ?_⟩,
      fun i => ?_, ?_, ?_⟩
    · by_cases hi : i = j
      · simpa [hi] using add_pos (hs0.1 j) hs0.2
      · simpa [hi] using hs0.1 i
    · simp [Finset.sum_add_distrib, hsum]
    · rw [hb i]
      simp [add_mul, Finset.sum_add_distrib]
    · have he : ev (fun i => s (Fin.castSucc i) + if i = j then s (Fin.last (k + 1)) else 0) f =
          ∑ m : Fin (k + 1), s (Fin.castSucc m) * f m + s (Fin.last (k + 1)) * f j := by
        simp [ev, add_mul, Finset.sum_add_distrib]
      rw [he, hl]
      have := mul_pos hs0.2 hd
      linarith
    · rw [ev_eq_of_eq_off hfg]
      have he : ev (fun i => s (Fin.castSucc i) + if i = j then s (Fin.last (k + 1)) else 0) f =
          ∑ m : Fin (k + 1), s (Fin.castSucc m) * f m + s (Fin.last (k + 1)) * f j := by
        simp [ev, add_mul, Finset.sum_add_distrib]
      rw [he, hl]
      simp only [↓reduceIte]
      have := mul_pos (hs0.1 j) hd
      linarith

variable {v} in
/-- The vertices of the band simplex are affinely independent. -/
theorem indep_band (hv : AffineIndependent ℚ v) (f : Fin (k + 1) → ℚ) (j : Fin (k + 1)) {c : ℚ}
    (hc : c ≠ f j) : AffineIndependent ℚ (bandVertices v f j c) := by
  refine affineIndependent_of_forall _ fun w h0 h1 => ?_
  rw [Fin.sum_univ_castSucc] at h0
  have hw' : ∀ m, w (Fin.castSucc m) + (if m = j then w (Fin.last (k + 1)) else 0) = 0 :=
    forall_of_affineIndependent hv
      (fun m => w (Fin.castSucc m) + if m = j then w (Fin.last (k + 1)) else 0)
      (by simpa [Finset.sum_add_distrib] using h0)
      (fun i => by
        have := h1 (Fin.castSucc i)
        rw [Fin.sum_univ_castSucc] at this
        simp only [bandVertices, lift, Fin.snoc_castSucc, Fin.snoc_last] at this
        simpa [add_mul, Finset.sum_add_distrib] using this)
  have hw : ∀ m, w (Fin.castSucc m) = -(if m = j then w (Fin.last (k + 1)) else 0) := fun m => by
    linarith [hw' m]
  have hl := h1 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hl
  simp only [bandVertices, lift, Fin.snoc_castSucc, Fin.snoc_last, hw,
    neg_mul, ite_mul, zero_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hl
  have hlast : w (Fin.last (k + 1)) = 0 := by
    have h : w (Fin.last (k + 1)) * (c - f j) = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hc)
  rw [Fin.forall_fin_succ']
  refine ⟨fun m => ?_, hlast⟩
  rw [hw m, hlast]
  simp

end elementary

end DiamondIntegral.Section8.Prism
