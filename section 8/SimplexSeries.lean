import «section 8».LatticeCone
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field

/-! The lattice-point series of an open rational simplex.

For `Δ ⊆ ℚⁿ` and an integer weight `wt x m`, the series is

  `Z(Δ, wt) = ∑_{m ≥ 1} ∑_{x ∈ ℤⁿ, x/m ∈ Δ} A^(wt x m) T^m`.

With `wt x m = −m ℓ(x/m)` this is the series of Hrushovski–Loeser, Lemma 8.5.2.
The main result: for an open simplex with affinely independent rational
vertices `w j` and a weight that is linear in `(x, m)` on the cone, the series
has limit `(−1)^(number of vertices)` at infinity, which is minus the Euler
characteristic of the simplex. The file uses Mathlib only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.SimplexSeries

open RationalSeries LatticeCone

variable {R : Type*} [CommRing R] (A : Rˣ) {n : ℕ}

/-- `∑_{m ≥ 1} ∑_{x ∈ ℤⁿ, x/m ∈ Δ} A^(wt x m) T^m`. -/
noncomputable def latticeSeries (Δ : Set (Fin n → ℚ)) (wt : (Fin n → ℤ) → ℕ → ℤ) :
    PowerSeries R :=
  PowerSeries.mk fun m : ℕ =>
    if m = 0 then 0
    else ∑ᶠ x ∈ {x : Fin n → ℤ | (fun i => (x i : ℚ) / m) ∈ Δ}, ((A ^ wt x m : Rˣ) : R)

/-- The open simplex with vertices `w j`. -/
def openSimplex {ι : Type*} [Fintype ι] (w : ι → Fin n → ℚ) : Set (Fin n → ℚ) :=
  {x | ∃ t : ι → ℚ, (∀ j, 0 < t j) ∧ ∑ j, t j = 1 ∧ ∀ i, x i = ∑ j, t j * w j i}

/-- The lattice `ℤⁿ × ℤ` of pairs `(x, m)`. -/
abbrev Lattice (n : ℕ) := (Fin n → ℤ) × ℤ

section cone

variable {ι : Type*} [Fintype ι] (g : ι → Fin n → ℤ) (d : ι → ℕ)

/-- The integral generator `(g j, d j)` over the vertex `g j / d j`. -/
def gen (j : ι) : Lattice n := (g j, (d j : ℤ))

/-- `x = ∑ c_j (g j, d j)` with rational coefficients. -/
def Rep (x : Lattice n) (c : ι → ℚ) : Prop :=
  (x.2 : ℚ) = ∑ j, c j * d j ∧ ∀ i, (x.1 i : ℚ) = ∑ j, c j * g j i

variable {g d}

theorem Rep.add {x y : Lattice n} {c c' : ι → ℚ} (h : Rep g d x c) (h' : Rep g d y c') :
    Rep g d (x + y) (c + c') := by
  refine ⟨?_, fun i => ?_⟩
  · simp [h.1, h'.1, add_mul, Finset.sum_add_distrib]
  · simp [h.2 i, h'.2 i, add_mul, Finset.sum_add_distrib]

theorem Rep.sub {x y : Lattice n} {c c' : ι → ℚ} (h : Rep g d x c) (h' : Rep g d y c') :
    Rep g d (x - y) (c - c') := by
  refine ⟨?_, fun i => ?_⟩
  · simp [h.1, h'.1, sub_mul, Finset.sum_sub_distrib]
  · simp [h.2 i, h'.2 i, sub_mul, Finset.sum_sub_distrib]

theorem Rep.eq {x y : Lattice n} {c : ι → ℚ} (h : Rep g d x c) (h' : Rep g d y c) : x = y := by
  refine Prod.ext (funext fun i => ?_) ?_
  · exact Int.cast_injective (α := ℚ) ((h.2 i).trans (h'.2 i).symm)
  · exact Int.cast_injective (α := ℚ) (h.1.trans h'.1.symm)

variable (g d) in
theorem rep_sum_gen (k : ι → ℕ) : Rep g d (∑ j, k j • gen g d j) (fun j => (k j : ℚ)) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [gen, Prod.snd_sum]
  · simp [gen, Prod.fst_sum, Finset.sum_apply]

variable (g d) in
/-- Linear independence of the generators, in coordinates. -/
def Independent : Prop :=
  ∀ c : ι → ℚ, ∑ j, c j * d j = 0 → (∀ i, ∑ j, c j * g j i = 0) → ∀ j, c j = 0

theorem Rep.unique (hLI : Independent g d) {x : Lattice n} {c c' : ι → ℚ} (h : Rep g d x c)
    (h' : Rep g d x c') : c = c' := by
  funext j
  have h0 := hLI (c - c')
    (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; rw [← h.1, ← h'.1, sub_self])
    (fun i => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; rw [← h.2 i, ← h'.2 i, sub_self])
    j
  exact sub_eq_zero.mp h0

theorem independent_of_affineIndependent {w : ι → Fin n → ℚ} (hw : AffineIndependent ℚ w)
    (hd : ∀ j, 0 < d j) (hg : ∀ j i, (g j i : ℚ) = d j * w j i) : Independent g d := by
  intro c h1 h2 j
  have hz := (affineIndependent_iff.mp hw) Finset.univ (fun j => c j * d j) h1
    (by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h2 i]
      exact Finset.sum_congr rfl fun j _ => by rw [hg j i]; ring)
    j (Finset.mem_univ j)
  have hdj : (d j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hd j).ne'
  exact (mul_eq_zero.mp hz).resolve_right hdj

variable (g d) in
/-- The lattice points of the half-open parallelepiped. -/
def parallelepiped : Set (Lattice n) :=
  {x | ∃ μ : ι → ℚ, Rep g d x μ ∧ ∀ j, 0 < μ j ∧ μ j ≤ 1}

theorem parallelepiped_finite : (parallelepiped g d).Finite := by
  classical
  let B : Lattice n := (fun i => ∑ j, |g j i|, ∑ j, (d j : ℤ))
  refine (Set.finite_Icc (-B) B).subset ?_
  rintro x ⟨μ, hx, hμ⟩
  have h2 : |(x.2 : ℚ)| ≤ ∑ j, (d j : ℚ) := by
    rw [hx.1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_pos (hμ j).1, Nat.abs_cast]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (hμ j).2
  have h1 : ∀ i, |(x.1 i : ℚ)| ≤ ∑ j, |(g j i : ℚ)| := by
    intro i
    rw [hx.2 i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_pos (hμ j).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hμ j).2
  have h2' : |x.2| ≤ ∑ j, (d j : ℤ) := by exact_mod_cast h2
  have h1' : ∀ i, |x.1 i| ≤ ∑ j, |g j i| := fun i => by exact_mod_cast h1 i
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
  · exact (abs_le.mp (h1' i)).1
  · exact (abs_le.mp h2').1
  · exact (abs_le.mp (h1' i)).2
  · exact (abs_le.mp h2').2

variable (g d) in
/-- The finite set `Π`. -/
noncomputable def parallelepipedFinset : Finset (Lattice n) := (parallelepiped_finite (g := g) (d := d)).toFinset

theorem mem_parallelepipedFinset {x : Lattice n} :
    x ∈ parallelepipedFinset g d ↔ ∃ μ : ι → ℚ, Rep g d x μ ∧ ∀ j, 0 < μ j ∧ μ j ≤ 1 :=
  Set.Finite.mem_toFinset _

/-- The degree `(x, m) ↦ m`. -/
def degHom (n : ℕ) : Lattice n →+ ℤ := AddMonoidHom.snd _ _

/-- The linear weight `(x, m) ↦ ∑ a_i x_i + b m`. -/
def weightHom (a : Fin n → ℤ) (b : ℤ) : Lattice n →+ ℤ :=
  AddMonoidHom.mk' (fun x => ∑ i, a i * x.1 i + b * x.2) (by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring)

/-- Decompositions `p + ∑ k_j v_j` are unique. -/
theorem param_injective (hLI : Independent g d) :
    ∀ p ∈ parallelepipedFinset g d, ∀ p' ∈ parallelepipedFinset g d, ∀ k k' : ι → ℕ,
      p + ∑ j, k j • gen g d j = p' + ∑ j, k' j • gen g d j → p = p' ∧ k = k' := by
  intro p hp p' hp' k k' he
  obtain ⟨μ, hpμ, hμ⟩ := mem_parallelepipedFinset.mp hp
  obtain ⟨μ', hpμ', hμ'⟩ := mem_parallelepipedFinset.mp hp'
  have hr := hpμ.add (rep_sum_gen g d k)
  have hr' := hpμ'.add (rep_sum_gen g d k')
  rw [he] at hr
  have hc := hr.unique hLI hr'
  have hk : k = k' := by
    funext j
    have hj := congrFun hc j
    simp only [Pi.add_apply] at hj
    have h1 : (k j : ℚ) < k' j + 1 := by linarith [(hμ j).1, (hμ j).2, (hμ' j).1, (hμ' j).2]
    have h2 : (k' j : ℚ) < k j + 1 := by linarith [(hμ j).1, (hμ j).2, (hμ' j).1, (hμ' j).2]
    have h1' : k j < k' j + 1 := by exact_mod_cast h1
    have h2' : k' j < k j + 1 := by exact_mod_cast h2
    omega
  refine ⟨?_, hk⟩
  subst hk
  exact add_right_cancel he

/-- The cone: the lattice points with positive coordinates in the generators. -/
theorem mem_coneSet_iff (x : Lattice n) :
    x ∈ coneSet (parallelepipedFinset g d) (gen g d) Finset.univ ↔
      ∃ c : ι → ℚ, Rep g d x c ∧ ∀ j, 0 < c j := by
  constructor
  · rintro ⟨p, hp, k, -, rfl⟩
    obtain ⟨μ, hpμ, hμ⟩ := mem_parallelepipedFinset.mp hp
    refine ⟨_, hpμ.add (rep_sum_gen g d k), fun j => ?_⟩
    simp only [Pi.add_apply]
    have : (0 : ℚ) ≤ k j := Nat.cast_nonneg _
    linarith [(hμ j).1]
  · rintro ⟨c, hx, hc⟩
    let k : ι → ℕ := fun j => ⌈c j⌉₊ - 1
    have hk : ∀ j, (k j : ℚ) = (⌈c j⌉₊ : ℚ) - 1 := fun j => by
      have h1 : 1 ≤ ⌈c j⌉₊ := Nat.ceil_pos.mpr (hc j)
      simp only [k]
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hp : Rep g d (x - ∑ j, k j • gen g d j) (c - fun j => (k j : ℚ)) :=
      hx.sub (rep_sum_gen g d k)
    refine ⟨x - ∑ j, k j • gen g d j, mem_parallelepipedFinset.mpr ⟨_, hp, fun j => ?_⟩, k,
      fun j hj => absurd (Finset.mem_univ j) hj, (sub_add_cancel _ _).symm⟩
    simp only [Pi.sub_apply, hk j]
    have h1 := Nat.le_ceil (c j)
    have h2 := Nat.ceil_lt_add_one (hc j).le
    constructor <;> linarith

omit [Fintype ι] in
theorem deg_gen_pos (hd : ∀ j, 0 < d j) (j : ι) : 0 < degHom n (gen g d j) := by
  simp only [degHom, gen, AddMonoidHom.coe_snd]
  exact_mod_cast hd j

theorem deg_nonneg (p : Lattice n) (hp : p ∈ parallelepipedFinset g d) : 0 ≤ degHom n p := by
  obtain ⟨μ, hpμ, hμ⟩ := mem_parallelepipedFinset.mp hp
  have h : (0 : ℚ) ≤ (p.2 : ℚ) := by
    rw [hpμ.1]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hμ j).1.le (Nat.cast_nonneg _)
  simp only [degHom, AddMonoidHom.coe_snd]
  exact_mod_cast h

theorem sum_gen_eq : ∑ j, gen g d j = ∑ j, (1 : ℕ) • gen g d j := by simp

theorem rep_sum_gen_one : Rep g d (∑ j, gen g d j) (fun _ => 1) := by
  rw [sum_gen_eq]
  simpa using rep_sum_gen g d (fun _ => 1)

theorem sum_gen_mem : ∑ j, gen g d j ∈ parallelepipedFinset g d :=
  mem_parallelepipedFinset.mpr ⟨_, rep_sum_gen_one, fun _ => ⟨one_pos, le_rfl⟩⟩

theorem deg_le_top (p : Lattice n) (hp : p ∈ parallelepipedFinset g d) :
    degHom n p ≤ degHom n (∑ j, gen g d j) := by
  obtain ⟨μ, hpμ, hμ⟩ := mem_parallelepipedFinset.mp hp
  have h : (p.2 : ℚ) ≤ ((∑ j, gen g d j : Lattice n).2 : ℚ) := by
    rw [hpμ.1, (rep_sum_gen_one (g := g) (d := d)).1]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hμ j).2 (Nat.cast_nonneg _)
  simp only [degHom, AddMonoidHom.coe_snd]
  exact_mod_cast h

theorem eq_top_of_deg_eq (hd : ∀ j, 0 < d j) (p : Lattice n)
    (hp : p ∈ parallelepipedFinset g d) (he : degHom n p = degHom n (∑ j, gen g d j)) :
    p = ∑ j, gen g d j := by
  obtain ⟨μ, hpμ, hμ⟩ := mem_parallelepipedFinset.mp hp
  have h : (p.2 : ℚ) = ((∑ j, gen g d j : Lattice n).2 : ℚ) := by
    simp only [degHom, AddMonoidHom.coe_snd] at he
    exact_mod_cast he
  rw [hpμ.1, (rep_sum_gen_one (g := g) (d := d)).1] at h
  have hall : ∀ j ∈ Finset.univ, μ j * d j = 1 * d j :=
    (Finset.sum_eq_sum_iff_of_le fun j _ =>
      mul_le_mul_of_nonneg_right (hμ j).2 (Nat.cast_nonneg _)).mp h
  have hμ1 : μ = fun _ => 1 := funext fun j =>
    mul_right_cancel₀ (Nat.cast_ne_zero.mpr (hd j).ne' : (d j : ℚ) ≠ 0) (hall j (Finset.mem_univ j))
  rw [hμ1] at hpμ
  exact hpμ.eq rep_sum_gen_one

/-- A lattice point `(y, m)` with `m ≥ 1` lies in the cone exactly when `y/m` lies in the
simplex. -/
theorem cone_iff_simplex {w : ι → Fin n → ℚ} (hd : ∀ j, 0 < d j)
    (hg : ∀ j i, (g j i : ℚ) = d j * w j i) (y : Fin n → ℤ) {m : ℕ} (hm : m ≠ 0) :
    (∃ c : ι → ℚ, Rep g d ((y, (m : ℤ)) : Lattice n) c ∧ ∀ j, 0 < c j) ↔
      (fun i => (y i : ℚ) / m) ∈ openSimplex w := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmpos : (0 : ℚ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hdpos : ∀ j, (0 : ℚ) < d j := fun j => Nat.cast_pos.mpr (hd j)
  constructor
  · rintro ⟨c, ⟨h2, h1⟩, hc⟩
    refine ⟨fun j => c j * d j / m, fun j => div_pos (mul_pos (hc j) (hdpos j)) hmpos, ?_,
      fun i => ?_⟩
    · rw [← Finset.sum_div, ← h2]
      simp only [Int.cast_natCast]
      exact div_self hm'
    · show (y i : ℚ) / m = ∑ j, c j * d j / m * w j i
      rw [h1 i, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hg j i]
      ring
  · rintro ⟨t, ht, hsum, hx⟩
    refine ⟨fun j => m * t j / d j, ⟨?_, fun i => ?_⟩,
      fun j => div_pos (mul_pos hmpos (ht j)) (hdpos j)⟩
    · show (((m : ℕ) : ℤ) : ℚ) = ∑ j, m * t j / d j * d j
      have h : ∀ j, (m : ℚ) * t j / d j * d j = m * t j := fun j =>
        div_mul_cancel₀ _ (hdpos j).ne'
      simp only [h, ← Finset.mul_sum, hsum, mul_one, Int.cast_natCast]
    · show (y i : ℚ) = ∑ j, m * t j / d j * g j i
      have hxi : (y i : ℚ) / m = ∑ j, t j * w j i := hx i
      have h : ∀ j, (m : ℚ) * t j / d j * g j i = m * (t j * w j i) := fun j => by
        rw [hg j i]
        have := (hdpos j).ne'
        field_simp
      simp only [h, ← Finset.mul_sum, ← hxi]
      field_simp

/-- The cone series is the lattice-point series of the simplex. -/
theorem series_eq_latticeSeries [Nonempty ι] {w : ι → Fin n → ℚ} (hd : ∀ j, 0 < d j)
    (hg : ∀ j i, (g j i : ℚ) = d j * w j i) (a : Fin n → ℤ) (b : ℤ)
    (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      wt x m = ∑ i, a i * x i + b * m) :
    series A (parallelepipedFinset g d) (gen g d) (degHom n) (weightHom a b) Finset.univ =
      latticeSeries A (openSimplex w) wt := by
  ext m
  simp only [series, latticeSeries, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst hm
    have hempty : level (parallelepipedFinset g d) (gen g d) (degHom n) Finset.univ
        ((0 : ℕ) : ℤ) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, hdeg⟩
      obtain ⟨c, hr, hc⟩ := (mem_coneSet_iff x).mp hx
      have hpos : (0 : ℚ) < x.2 := by
        rw [hr.1]
        exact Finset.sum_pos (fun j _ => mul_pos (hc j) (Nat.cast_pos.mpr (hd j)))
          Finset.univ_nonempty
      have hx2 : x.2 = 0 := by simpa [degHom] using hdeg
      rw [hx2] at hpos
      simp at hpos
    rw [hempty, finsum_mem_empty]
    simp
  · simp only [hm, ↓reduceIte]
    have hlev : level (parallelepipedFinset g d) (gen g d) (degHom n) Finset.univ (m : ℤ) =
        (fun y : Fin n → ℤ => ((y, (m : ℤ)) : Lattice n)) ''
          {y | (fun i => (y i : ℚ) / m) ∈ openSimplex w} := by
      ext x
      constructor
      · rintro ⟨hx, hdeg⟩
        have hx2 : x.2 = (m : ℤ) := hdeg
        have hxe : x = (x.1, (m : ℤ)) := Prod.ext rfl hx2
        refine ⟨x.1, ?_, hxe.symm⟩
        have h := (mem_coneSet_iff x).mp hx
        rw [hxe] at h
        exact (cone_iff_simplex hd hg x.1 hm).mp h
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(mem_coneSet_iff _).mpr ((cone_iff_simplex hd hg y hm).mpr hy), rfl⟩
    rw [hlev, finsum_mem_image fun y _ y' _ h => (Prod.ext_iff.mp h).1]
    refine finsum_mem_congr rfl fun y hy => ?_
    have hw' : weightHom a b ((y, (m : ℤ)) : Lattice n) = wt y m := (hwt y m hy).symm
    simp only [weight, hw']

/-- The series of an open simplex given with integral generators. -/
theorem hasLimit_openSimplex_of_generators [Nonempty ι] {w : ι → Fin n → ℚ}
    (hw : AffineIndependent ℚ w) (hd : ∀ j, 0 < d j) (hg : ∀ j i, (g j i : ℚ) = d j * w j i)
    (a : Fin n → ℤ) (b : ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      wt x m = ∑ i, a i * x i + b * m) :
    HasLimit A (latticeSeries A (openSimplex w) wt) ((-1) ^ Fintype.card ι) := by
  classical
  have hLI := independent_of_affineIndependent hw hd hg
  rw [← series_eq_latticeSeries A hd hg a b wt hwt]
  exact hasLimit_series A _ _ _ _ (param_injective hLI) (deg_gen_pos hd) deg_nonneg sum_gen_mem
    deg_le_top (eq_top_of_deg_eq hd)

end cone

theorem num_mul_cast (q : ℚ) {D : ℕ} (h : q.den ∣ D) : (((q * D).num : ℤ) : ℚ) = q * D := by
  obtain ⟨k, rfl⟩ := h
  have hq : q * ((q.den * k : ℕ) : ℚ) = ((q.num * k : ℤ) : ℚ) := by
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  rw [hq, Rat.num_intCast]

/-- **The series of an open rational simplex.** For affinely independent vertices `w j ∈ ℚⁿ`
and a weight that is linear in `(x, m)` on the cone over the simplex, the lattice-point series
is in `R[T]†`, of degree `0`, with limit `(−1)^(number of vertices)`: minus the Euler
characteristic of the open simplex. -/
theorem hasLimit_openSimplex {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → Fin n → ℚ)
    (hw : AffineIndependent ℚ w) (a : Fin n → ℤ) (b : ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex w →
      wt x m = ∑ i, a i * x i + b * m) :
    HasLimit A (latticeSeries A (openSimplex w) wt) ((-1) ^ Fintype.card ι) := by
  let d : ι → ℕ := fun j => ∏ i, (w j i).den
  let g : ι → Fin n → ℤ := fun j i => (w j i * d j).num
  have hd : ∀ j, 0 < d j := fun j => Finset.prod_pos fun i _ => Rat.den_pos _
  have hg : ∀ j i, (g j i : ℚ) = d j * w j i := fun j i => by
    rw [mul_comm]
    exact num_mul_cast _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact hasLimit_openSimplex_of_generators A hw hd hg a b wt hwt

/-! ### Additivity over a finite disjoint union of simplices -/

theorem lattice_finite_of_bounded {Δ : Set (Fin n → ℚ)} {B : ℚ}
    (hB : ∀ x ∈ Δ, ∀ i, |x i| ≤ B) {m : ℕ} (hm : m ≠ 0) :
    {x : Fin n → ℤ | (fun i => (x i : ℚ) / m) ∈ Δ}.Finite := by
  have hmpos : (0 : ℚ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  refine (Set.finite_Icc (fun _ : Fin n => -⌈B * m⌉) (fun _ => ⌈B * m⌉)).subset ?_
  intro x hx
  have h : ∀ i, |(x i : ℚ)| ≤ ⌈B * m⌉ := fun i => by
    have h1 : |(x i : ℚ) / m| ≤ B := hB _ hx i
    rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos] at h1
    exact h1.trans (Int.le_ceil _)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (h i)).1
    exact_mod_cast this
  · have := (abs_le.mp (h i)).2
    exact_mod_cast this

theorem openSimplex_bounded {ι : Type*} [Fintype ι] (w : ι → Fin n → ℚ) :
    ∀ x ∈ openSimplex w, ∀ i, |x i| ≤ ∑ j, ∑ i', |w j i'| := by
  rintro x ⟨t, ht, hsum, hx⟩ i
  rw [hx i]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have htj : t j ≤ 1 := hsum ▸ Finset.single_le_sum (fun k _ => (ht k).le) (Finset.mem_univ j)
  rw [abs_mul, abs_of_pos (ht j)]
  exact (mul_le_of_le_one_left (abs_nonneg _) htj).trans
    (Finset.single_le_sum (f := fun i' => |w j i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- The series is additive over finite disjoint unions of bounded sets. -/
theorem latticeSeries_iUnion {κ : Type*} [Fintype κ] (Δ : κ → Set (Fin n → ℚ))
    (hdisj : Pairwise (Function.onFun Disjoint Δ))
    (hB : ∀ k, ∃ B : ℚ, ∀ x ∈ Δ k, ∀ i, |x i| ≤ B) (wt : (Fin n → ℤ) → ℕ → ℤ) :
    latticeSeries A (⋃ k, Δ k) wt = ∑ k, latticeSeries A (Δ k) wt := by
  ext m
  simp only [latticeSeries, map_sum, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    have hset : {x : Fin n → ℤ | (fun i => (x i : ℚ) / m) ∈ ⋃ k, Δ k} =
        ⋃ k, {x : Fin n → ℤ | (fun i => (x i : ℚ) / m) ∈ Δ k} := by
      ext x
      simp
    rw [hset, finsum_mem_iUnion ?_ ?_, finsum_eq_sum_of_fintype]
    · intro k k' hkk'
      exact Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp (hdisj hkk') hx hx'
    · intro k
      obtain ⟨B, hB⟩ := hB k
      exact lattice_finite_of_bounded hB hm

/-- **Lemma 8.5.2 of Hrushovski–Loeser for a triangulated set.** If `Δ` is a finite disjoint
union of open simplices with affinely independent rational vertices and the weight is linear
in `(x, m)` on the cone over each simplex, then the lattice-point series of `Δ` is in `R[T]†`,
of degree `≤ 0`, and its limit is `∑_σ (−1)^(dim σ + 1)`, minus the Euler characteristic. -/
theorem hasLimit_of_triangulation {κ : Type*} [Fintype κ] (ι : κ → Type*)
    [∀ k, Fintype (ι k)] [∀ k, Nonempty (ι k)] (w : ∀ k, ι k → Fin n → ℚ)
    (hw : ∀ k, AffineIndependent ℚ (w k))
    (hdisj : Pairwise (Function.onFun Disjoint fun k => openSimplex (w k)))
    (a : κ → Fin n → ℤ) (b : κ → ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (k : κ) (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ openSimplex (w k) →
      wt x m = ∑ i, a k i * x i + b k * m) :
    HasLimit A (latticeSeries A (⋃ k, openSimplex (w k)) wt)
      (∑ k, (-1) ^ Fintype.card (ι k)) := by
  rw [latticeSeries_iUnion A _ hdisj fun k => ⟨_, openSimplex_bounded (w k)⟩]
  exact HasLimit.sum A Finset.univ _ _ fun k _ =>
    hasLimit_openSimplex A (w k) (hw k) (a k) (b k) wt (hwt k)

end DiamondIntegral.Section8.SimplexSeries
