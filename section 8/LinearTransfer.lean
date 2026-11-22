import «section 8».Triangulation
import Mathlib.Algebra.Order.Module.Defs

/-! Rational points of linear sign conditions in an ordered `ℚ`-vector space.

Let `V` be a linearly ordered `ℚ`-vector space and `e > 0` a unit. An affine function with
rational coefficients is evaluated on `Vⁿ` with its constant term multiplied by `e`
(`AffFun.evalV`); the point `x ∈ ℚⁿ` corresponds to `x • e ∈ Vⁿ`.

* `exists_rat_signs` (transfer): every sign pattern of finitely many affine functions that occurs
  at a point of `Vⁿ` occurs at a point of `ℚⁿ`. The proof is Fourier–Motzkin elimination of the
  last coordinate, as in `exists_adapted_triangulation`.
* `exists_interp`: on a cylindrical simplex any vertex values are interpolated by an affine
  function.
* `VCell`: the cells of `Vⁿ` built from the point by graphs and bands of affine functions over the
  base; this is the shape of the cylindrical cells of the value group.
* `exists_vcell_partition`: if `D ⊆ ℚⁿ` is a bounded union of sign classes, the union of the
  corresponding sign classes in `Vⁿ` is partitioned into `VCell`s, one for each simplex of a
  triangulation of `D`, of the same dimension.

The file uses Mathlib only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.Prism

open SimplexSeries HeightChains

variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module ℚ V]
  [PosSMulStrictMono ℚ V]

/-! ### Signs of scalar multiples -/

theorem sign_smul_pos {e : V} (he : 0 < e) (q : ℚ) : SignType.sign (q • e) = SignType.sign q := by
  rcases lt_trichotomy q 0 with h | h | h
  · have : 0 < (-q) • e := smul_pos (neg_pos.mpr h) he
    rw [neg_smul, neg_pos] at this
    rw [sign_neg this, sign_neg h]
  · simp [h]
  · rw [sign_pos (smul_pos h he), sign_pos h]

theorem sign_smul (q : ℚ) (w : V) :
    SignType.sign (q • w) = SignType.sign q * SignType.sign w := by
  rcases lt_trichotomy w 0 with hw | hw | hw
  · have h1 : SignType.sign (q • (-w)) = SignType.sign q := sign_smul_pos (neg_pos.mpr hw) q
    rw [smul_neg, Left.sign_neg] at h1
    rw [sign_neg hw]
    calc SignType.sign (q • w) = -(-SignType.sign (q • w)) := (neg_neg _).symm
      _ = SignType.sign q * -1 := by rw [h1]; simp
  · simp [hw]
  · rw [sign_smul_pos hw q, sign_pos hw, mul_one]

namespace AffFun

variable {n : ℕ}

/-- The value at a point of `Vⁿ`, the constant term being multiplied by the unit `e`. -/
def evalV (e : V) (g : AffFun n) (z : Fin n → V) : V := ∑ i, g.coeff i • z i + g.const • e

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_emb (e : V) (g : AffFun n) (x : Fin n → ℚ) :
    g.evalV e (fun i => x i • e) = g.eval x • e := by
  simp only [evalV, eval, smul_smul, add_smul, Finset.sum_smul]

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_sub (e : V) (g h : AffFun n) (z : Fin n → V) :
    (g.sub h).evalV e z = g.evalV e z - h.evalV e z := by
  simp only [evalV, sub, sub_smul, Finset.sum_sub_distrib]
  abel

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_const (e : V) (a : ℚ) (z : Fin n → V) : (constFun n a).evalV e z = a • e := by
  simp [evalV, constFun]

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_eq (e : V) (g : AffFun (n + 1)) (z : Fin (n + 1) → V) :
    g.evalV e z = g.base.evalV e (fun i => z (Fin.castSucc i)) + g.lead • z (Fin.last n) := by
  simp only [evalV, base, lead, Fin.sum_univ_castSucc]
  abel

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_eq_solve (e : V) (g : AffFun (n + 1)) (h : g.lead ≠ 0) (z : Fin (n + 1) → V) :
    g.evalV e z = g.lead • (z (Fin.last n) - g.solve.evalV e (fun i => z (Fin.castSucc i))) := by
  have hs : g.lead • g.solve.evalV e (fun i => z (Fin.castSucc i)) =
      -g.base.evalV e (fun i => z (Fin.castSucc i)) := by
    simp only [evalV, solve, base, smul_add, Finset.smul_sum, smul_smul, neg_add, ←
      Finset.sum_neg_distrib, ← neg_smul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_div_cancel₀ _ h]
    · rw [mul_div_cancel₀ _ h]
  rw [evalV_eq, smul_sub, hs]
  abel

/-- The function on `ℚⁿ⁺¹` given by a function of the first `n` coordinates. -/
def liftFun (g : AffFun n) : AffFun (n + 1) := ⟨Fin.snoc g.coeff 0, g.const⟩

/-- The last coordinate. -/
def lastFun (n : ℕ) : AffFun (n + 1) := ⟨Fin.snoc (fun _ => 0) 1, 0⟩

theorem eval_liftFun (g : AffFun n) (z : Fin (n + 1) → ℚ) :
    g.liftFun.eval z = g.eval (fun i => z (Fin.castSucc i)) := by
  simp [eval, liftFun, Fin.sum_univ_castSucc]

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_liftFun (e : V) (g : AffFun n) (z : Fin (n + 1) → V) :
    g.liftFun.evalV e z = g.evalV e (fun i => z (Fin.castSucc i)) := by
  simp [evalV, liftFun, Fin.sum_univ_castSucc]

theorem eval_lastFun (z : Fin (n + 1) → ℚ) : (lastFun n).eval z = z (Fin.last n) := by
  simp [eval, lastFun, Fin.sum_univ_castSucc]

omit [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem evalV_lastFun (e : V) (z : Fin (n + 1) → V) : (lastFun n).evalV e z = z (Fin.last n) := by
  simp [evalV, lastFun, Fin.sum_univ_castSucc]

/-- `g + a • (lastFun − h)` for `g h` on the first `n` coordinates. -/
def addLast (g h : AffFun n) (a : ℚ) : AffFun (n + 1) :=
  ⟨Fin.snoc (fun i => g.coeff i - a * h.coeff i) a, g.const - a * h.const⟩

theorem eval_addLast (g h : AffFun n) (a : ℚ) (z : Fin (n + 1) → ℚ) :
    (addLast g h a).eval z =
      g.eval (fun i => z (Fin.castSucc i)) + a * (z (Fin.last n) - h.eval (fun i => z (Fin.castSucc i))) := by
  simp only [eval, addLast, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, sub_mul,
    Finset.sum_sub_distrib]
  have : ∑ x, a * h.coeff x * z (Fin.castSucc x) = a * ∑ x, h.coeff x * z (Fin.castSucc x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

end AffFun

/-! ### Transfer of sign patterns -/

/-- Between two finite sets of rationals, the first below the second, there is a rational. -/
theorem exists_rat_between_finsets (S T : Finset ℚ) (h : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃ r : ℚ, (∀ s ∈ S, s < r) ∧ ∀ t ∈ T, r < t := by
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · refine ⟨(S.max' hS + T.min' hT) / 2, fun s hs => ?_, fun t ht => ?_⟩
      · have h1 := S.le_max' s hs
        have h2 := h _ (S.max'_mem hS) _ (T.min'_mem hT)
        linarith
      · have h1 := T.min'_le t ht
        have h2 := h _ (S.max'_mem hS) _ (T.min'_mem hT)
        linarith
    · refine ⟨S.max' hS + 1, fun s hs => ?_, fun t ht => absurd ⟨t, ht⟩ hT⟩
      have := S.le_max' s hs
      linarith
  · by_cases hT : T.Nonempty
    · refine ⟨T.min' hT - 1, fun s hs => absurd ⟨s, hs⟩ hS, fun t ht => ?_⟩
      have := T.min'_le t ht
      linarith
    · exact ⟨0, fun s hs => absurd ⟨s, hs⟩ hS, fun t ht => absurd ⟨t, ht⟩ hT⟩

omit [Module ℚ V] [PosSMulStrictMono ℚ V] in
/-- A point `y ∈ V` placed among values `b i` is matched by a rational placed in the same way
among rationals `a i` ordered like the `b i`. -/
theorem exists_rat_config {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ) (b : ι → V)
    (y : V) (hab : ∀ i ∈ s, ∀ j ∈ s, SignType.sign (a i - a j) = SignType.sign (b i - b j)) :
    ∃ r : ℚ, ∀ i ∈ s, SignType.sign (r - a i) = SignType.sign (y - b i) := by
  classical
  by_cases hy : ∃ i ∈ s, y = b i
  · obtain ⟨i, hi, rfl⟩ := hy
    exact ⟨a i, fun j hj => hab i hi j hj⟩
  push Not at hy
  obtain ⟨r, hlo, hhi⟩ := exists_rat_between_finsets ((s.filter fun i => b i < y).image a)
    ((s.filter fun i => y < b i).image a) (by
      intro p hp q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨his, hiy⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjs, hjy⟩ := Finset.mem_filter.mp hj
      have := hab i his j hjs
      rw [sign_neg (sub_neg.mpr (hiy.trans hjy)), sign_eq_neg_one_iff, sub_neg] at this
      exact this)
  refine ⟨r, fun i hi => ?_⟩
  rcases lt_or_gt_of_ne (hy i hi) with h | h
  · have hr := hhi (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, rfl⟩)
    rw [sign_neg (sub_neg.mpr hr), sign_neg (sub_neg.mpr h)]
  · have hr := hlo (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, rfl⟩)
    rw [sign_pos (sub_pos.mpr hr), sign_pos (sub_pos.mpr h)]

/-- **Transfer.** Every sign pattern of finitely many rational affine functions that occurs in
`Vⁿ` occurs in `ℚⁿ`. -/
theorem exists_rat_signs {e : V} (he : 0 < e) :
    ∀ (n : ℕ) (G : List (AffFun n)) (z : Fin n → V),
      ∃ x : Fin n → ℚ, ∀ g ∈ G, SignType.sign (g.eval x) = SignType.sign (g.evalV e z) := by
  intro n
  induction n with
  | zero =>
    intro G z
    refine ⟨fun i => i.elim0, fun g _ => ?_⟩
    simp [AffFun.eval, AffFun.evalV, sign_smul_pos he]
  | succ n ih =>
    intro G z
    classical
    let Φ : List (AffFun n) := (G.filter fun g => decide (g.lead ≠ 0)).map AffFun.solve
    let G' : List (AffFun n) := (G.filter fun g => decide (g.lead = 0)).map AffFun.base ++
      (Φ ×ˢ Φ).map fun p => p.1.sub p.2
    let z' : Fin n → V := fun i => z (Fin.castSucc i)
    obtain ⟨x', hx'⟩ := ih G' z'
    obtain ⟨r, hr⟩ := exists_rat_config Φ.toFinset (fun φ => φ.eval x') (fun φ => φ.evalV e z')
      (z (Fin.last n)) (by
        intro φ hφ ψ hψ
        have := hx' (φ.sub ψ) (List.mem_append_right _ (List.mem_map.mpr
          ⟨(φ, ψ), List.pair_mem_product.mpr ⟨List.mem_toFinset.mp hφ, List.mem_toFinset.mp hψ⟩,
            rfl⟩))
        rwa [AffFun.eval_sub, AffFun.evalV_sub] at this)
    refine ⟨Fin.snoc x' r, fun g hg => ?_⟩
    have hc : (fun i => (Fin.snoc x' r : Fin (n + 1) → ℚ) (Fin.castSucc i)) = x' := by
      funext i; simp
    by_cases hlead : g.lead = 0
    · rw [AffFun.eval_eq, AffFun.evalV_eq, hlead, zero_mul, zero_smul, add_zero, add_zero, hc]
      exact hx' g.base (List.mem_append_left _ (List.mem_map.mpr
        ⟨g, List.mem_filter.mpr ⟨hg, by simpa using hlead⟩, rfl⟩))
    · rw [AffFun.eval_eq_solve g hlead, AffFun.evalV_eq_solve e g hlead, sign_mul, sign_smul, hc,
        Fin.snoc_last]
      congr 1
      exact hr g.solve (List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨g, List.mem_filter.mpr ⟨hg, by simpa using hlead⟩, rfl⟩))

/-! ### Realizations of unions of sign classes -/

section realization

variable {n : ℕ}

/-- The union of the sign classes in `Vⁿ` of the functions in `G` that meet `D ⊆ ℚⁿ`. -/
def realV (e : V) (G : List (AffFun n)) (D : Set (Fin n → ℚ)) : Set (Fin n → V) :=
  {z | ∃ x ∈ D, ∀ g ∈ G, SignType.sign (g.eval x) = SignType.sign (g.evalV e z)}

/-- `S ⊆ Vⁿ` is a union of sign classes of the functions in `G`. -/
def SaturatedV (e : V) (G : List (AffFun n)) (S : Set (Fin n → V)) : Prop :=
  ∀ z w, (∀ g ∈ G, SignType.sign (g.evalV e z) = SignType.sign (g.evalV e w)) → (z ∈ S ↔ w ∈ S)

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem mem_realV_iff {e : V} {G : List (AffFun n)} {D : Set (Fin n → ℚ)}
    (hD : Constructible G D) {z : Fin n → V} {x : Fin n → ℚ}
    (hx : ∀ g ∈ G, SignType.sign (g.eval x) = SignType.sign (g.evalV e z)) :
    z ∈ realV e G D ↔ x ∈ D := by
  constructor
  · rintro ⟨x₀, hx₀, h₀⟩
    exact (hD x₀ x fun g hg => (h₀ g hg).trans (hx g hg).symm).mp hx₀
  · exact fun h => ⟨x, h, hx⟩

/-- A union of sign classes in `Vⁿ` is the realization of its rational points. -/
theorem realV_of_saturated {e : V} (he : 0 < e) {G : List (AffFun n)} {S : Set (Fin n → V)}
    (hS : SaturatedV e G S) :
    Constructible G {x | (fun i => x i • e) ∈ S} ∧ realV e G {x | (fun i => x i • e) ∈ S} = S := by
  have hemb : ∀ x : Fin n → ℚ, ∀ g ∈ G,
      SignType.sign (g.eval x) = SignType.sign (g.evalV e (fun i => x i • e)) := fun x g _ => by
    rw [AffFun.evalV_emb, sign_smul_pos he]
  refine ⟨fun x y hxy => hS _ _ fun g hg => ?_, Set.Subset.antisymm ?_ ?_⟩
  · rw [← hemb x g hg, ← hemb y g hg, hxy g hg]
  · rintro z ⟨x, hx, hxz⟩
    exact (hS _ z fun g hg => (hemb x g hg).symm.trans (hxz g hg)).mp hx
  · intro z hz
    obtain ⟨x, hx⟩ := exists_rat_signs he n G z
    exact ⟨x, (hS _ z fun g hg => (hemb x g hg).symm.trans (hx g hg)).mpr hz, hx⟩

end realization

/-! ### Interpolation on cylindrical simplices -/

theorem exists_interp {n d : ℕ} {v : Fin (d + 1) → Fin n → ℚ} (hv : IsCyl v) :
    ∀ u : Fin (d + 1) → ℚ, ∃ φ : AffFun n, ∀ j, φ.eval (v j) = u j := by
  induction hv with
  | point v =>
    intro u
    refine ⟨AffFun.constFun 0 (u 0), fun j => ?_⟩
    rw [AffFun.eval_const, show j = 0 from Fin.fin_one_eq_zero j]
  | graph v w _ ih =>
    intro u
    obtain ⟨φ, hφ⟩ := ih u
    refine ⟨φ.liftFun, fun j => ?_⟩
    rw [AffFun.eval_liftFun]
    simp only [lift, Fin.snoc_castSucc]
    exact hφ j
  | band v f j c h _ ih =>
    intro u
    obtain ⟨φ, hφ⟩ := ih (fun i => u (Fin.castSucc i))
    obtain ⟨ψ, hψ⟩ := ih f
    refine ⟨AffFun.addLast φ ψ ((u (Fin.last _) - u (Fin.castSucc j)) / (c - f j)), fun i => ?_⟩
    rw [AffFun.eval_addLast]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [bandVertices, Fin.snoc_last, Fin.snoc_castSucc]
      rw [hφ, hψ]
      have : c - f j ≠ 0 := sub_ne_zero.mpr h.ne'
      field_simp
      ring
    · simp only [bandVertices, Fin.snoc_castSucc, lift, Fin.snoc_last]
      rw [hφ, hψ, sub_self, mul_zero, add_zero]

/-! ### Cells of `Vⁿ` -/

/-- Cells of `Vⁿ` built from the point by graphs and bands of affine functions over the first
`n` coordinates; the second index is the dimension. -/
inductive VCell (e : V) : (n d : ℕ) → Set (Fin n → V) → Prop
  | point : VCell e 0 0 Set.univ
  | graph {n d : ℕ} {C : Set (Fin n → V)} (hC : VCell e n d C) (φ : AffFun n) :
      VCell e (n + 1) d {z | (fun i => z (Fin.castSucc i)) ∈ C ∧
        z (Fin.last n) = φ.evalV e (fun i => z (Fin.castSucc i))}
  | band {n d : ℕ} {C : Set (Fin n → V)} (hC : VCell e n d C) (φ ψ : AffFun n)
      (hlt : ∀ z ∈ C, φ.evalV e z < ψ.evalV e z) :
      VCell e (n + 1) (d + 1) {z | (fun i => z (Fin.castSucc i)) ∈ C ∧
        φ.evalV e (fun i => z (Fin.castSucc i)) < z (Fin.last n) ∧
        z (Fin.last n) < ψ.evalV e (fun i => z (Fin.castSucc i))}

section constraints

variable {n : ℕ}

/-- The points of `ℚⁿ` at which each function has the prescribed sign. -/
def satQ (C : List (AffFun n × SignType)) : Set (Fin n → ℚ) :=
  {x | ∀ p ∈ C, SignType.sign (p.1.eval x) = p.2}

/-- The points of `Vⁿ` at which each function has the prescribed sign. -/
def satV (e : V) (C : List (AffFun n × SignType)) : Set (Fin n → V) :=
  {z | ∀ p ∈ C, SignType.sign (p.1.evalV e z) = p.2}

/-- Constraints on the first `n` coordinates, as constraints on `ℚⁿ⁺¹`. -/
def liftC (C : List (AffFun n × SignType)) : List (AffFun (n + 1) × SignType) :=
  C.map fun p => (p.1.liftFun, p.2)

theorem mem_satQ_liftC (C : List (AffFun n × SignType)) (x : Fin (n + 1) → ℚ) :
    (∀ p ∈ liftC C, SignType.sign (p.1.eval x) = p.2) ↔ (fun i => x (Fin.castSucc i)) ∈ satQ C := by
  constructor
  · intro h p hp
    have := h (p.1.liftFun, p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rwa [AffFun.eval_liftFun] at this
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    show SignType.sign (p.1.liftFun.eval x) = p.2
    rw [AffFun.eval_liftFun]
    exact h p hp

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem mem_satV_liftC (e : V) (C : List (AffFun n × SignType)) (z : Fin (n + 1) → V) :
    (∀ p ∈ liftC C, SignType.sign (p.1.evalV e z) = p.2) ↔
      (fun i => z (Fin.castSucc i)) ∈ satV e C := by
  constructor
  · intro h p hp
    have := h (p.1.liftFun, p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rwa [AffFun.evalV_liftFun] at this
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    show SignType.sign (p.1.liftFun.evalV e z) = p.2
    rw [AffFun.evalV_liftFun]
    exact h p hp

theorem mem_satQ_liftC_append (C : List (AffFun n × SignType)) (L : List (AffFun (n + 1) × SignType))
    (x : Fin (n + 1) → ℚ) :
    x ∈ satQ (liftC C ++ L) ↔
      (fun i => x (Fin.castSucc i)) ∈ satQ C ∧ ∀ p ∈ L, SignType.sign (p.1.eval x) = p.2 := by
  show (∀ p ∈ liftC C ++ L, SignType.sign (p.1.eval x) = p.2) ↔ _
  rw [List.forall_mem_append, mem_satQ_liftC]

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem mem_satV_liftC_append (e : V) (C : List (AffFun n × SignType))
    (L : List (AffFun (n + 1) × SignType)) (z : Fin (n + 1) → V) :
    z ∈ satV e (liftC C ++ L) ↔
      (fun i => z (Fin.castSucc i)) ∈ satV e C ∧ ∀ p ∈ L, SignType.sign (p.1.evalV e z) = p.2 := by
  show (∀ p ∈ liftC C ++ L, SignType.sign (p.1.evalV e z) = p.2) ↔ _
  rw [List.forall_mem_append, mem_satV_liftC]

end constraints

/-- A cylindrical simplex is given by sign conditions, and the same conditions in `Vⁿ` give a
cell of the same dimension. -/
theorem cyl_realization {e : V} (he : 0 < e) {n d : ℕ} {v : Fin (d + 1) → Fin n → ℚ}
    (hv : IsCyl v) :
    ∃ C : List (AffFun n × SignType), openSimplex v = satQ C ∧ VCell e n d (satV e C) := by
  induction hv with
  | point v =>
    refine ⟨[], ?_, ?_⟩
    · ext x
      refine iff_of_true ((mem_openSimplex_iff _ _).mpr ⟨fun _ => 1, ⟨fun _ => one_pos, by simp⟩,
        fun i => i.elim0⟩) fun p hp => absurd hp List.not_mem_nil
    · have : satV e ([] : List (AffFun 0 × SignType)) = Set.univ :=
        Set.eq_univ_of_forall fun z p hp => absurd hp List.not_mem_nil
      rw [this]
      exact VCell.point
  | @graph n d v w hv ih =>
    obtain ⟨C, hC, hcell⟩ := ih
    obtain ⟨φ, hφ⟩ := exists_interp hv w
    let gg : AffFun (n + 1) := (AffFun.lastFun n).sub φ.liftFun
    refine ⟨liftC C ++ [(gg, 0)], ?_, ?_⟩
    · ext x
      rw [mem_satQ_liftC_append, List.forall_mem_singleton, ← hC]
      show x ∈ openSimplex (lift v w) ↔ _ ∧ SignType.sign (gg.eval x) = 0
      rw [AffFun.eval_sub, AffFun.eval_lastFun, AffFun.eval_liftFun, sign_eq_zero_iff, sub_eq_zero,
        mem_graph_iff]
      constructor
      · rintro ⟨t, ht, hb, hz⟩
        refine ⟨(mem_openSimplex_iff _ _).mpr ⟨t, ht, hb⟩, ?_⟩
        rw [hz, AffFun.eval_bary φ v ht hb]
        simp only [hφ]
      · rintro ⟨hx, hz⟩
        obtain ⟨t, ht, hb⟩ := (mem_openSimplex_iff _ _).mp hx
        refine ⟨t, ht, hb, ?_⟩
        rw [hz, AffFun.eval_bary φ v ht hb]
        simp only [hφ]
    · have hset : satV e (liftC C ++ [(gg, 0)]) =
          {z | (fun i => z (Fin.castSucc i)) ∈ satV e C ∧
            z (Fin.last n) = φ.evalV e (fun i => z (Fin.castSucc i))} := by
        ext z
        rw [mem_satV_liftC_append, List.forall_mem_singleton]
        show _ ∧ SignType.sign (gg.evalV e z) = 0 ↔ _ ∧ _
        rw [AffFun.evalV_sub, AffFun.evalV_lastFun, AffFun.evalV_liftFun, sign_eq_zero_iff,
          sub_eq_zero]
      rw [hset]
      exact VCell.graph hcell φ
  | @band n d v f j c h hv ih =>
    obtain ⟨C, hC, hcell⟩ := ih
    obtain ⟨φ, hφ⟩ := exists_interp hv f
    obtain ⟨ψ, hψ⟩ := exists_interp hv (Function.update f j c)
    have hfg : ∀ i, i ≠ j → f i = Function.update f j c i := fun i hi => by
      rw [Function.update_of_ne hi]
    have hgj : Function.update f j c j = c := Function.update_self j c f
    have hval : ∀ t, IsBary t → ∀ x : Fin n → ℚ, (∀ i, x i = ∑ k, t k * v k i) →
        φ.eval x = ev t f ∧ ψ.eval x = ev t (Function.update f j c) := fun t ht x hx => by
      refine ⟨?_, ?_⟩
      · rw [AffFun.eval_bary φ v ht hx]; simp only [hφ]
      · rw [AffFun.eval_bary ψ v ht hx]; simp only [hψ]
    have hltQ : ∀ x ∈ satQ C, φ.eval x < ψ.eval x := by
      intro x hx
      rw [← hC] at hx
      obtain ⟨t, ht, hb⟩ := (mem_openSimplex_iff _ _).mp hx
      obtain ⟨h1, h2⟩ := hval t ht x hb
      rw [h1, h2, ev_eq_of_eq_off hfg, hgj]
      have := mul_pos (ht.1 j) (sub_pos.mpr h)
      linarith
    let g1 : AffFun (n + 1) := (AffFun.lastFun n).sub φ.liftFun
    let g2 : AffFun (n + 1) := ψ.liftFun.sub (AffFun.lastFun n)
    refine ⟨liftC C ++ [(g1, 1), (g2, 1)], ?_, ?_⟩
    · ext x
      rw [mem_satQ_liftC_append, List.forall_mem_cons, List.forall_mem_singleton, ← hC]
      show x ∈ openSimplex (bandVertices v f j c) ↔
        _ ∧ SignType.sign (g1.eval x) = 1 ∧ SignType.sign (g2.eval x) = 1
      rw [AffFun.eval_sub, AffFun.eval_sub, AffFun.eval_lastFun, AffFun.eval_liftFun,
        AffFun.eval_liftFun, sign_eq_one_iff, sign_eq_one_iff, sub_pos, sub_pos]
      conv_lhs => rw [← hgj, ← band_eq_simplex v hfg (by rw [hgj]; exact h)]
      constructor
      · rintro ⟨t, ht, hb, h1, h2⟩
        obtain ⟨e1, e2⟩ := hval t ht _ hb
        exact ⟨(mem_openSimplex_iff _ _).mpr ⟨t, ht, hb⟩, by rw [e1]; exact h1, by rw [e2]; exact h2⟩
      · rintro ⟨hx, h1, h2⟩
        obtain ⟨t, ht, hb⟩ := (mem_openSimplex_iff _ _).mp hx
        obtain ⟨e1, e2⟩ := hval t ht _ hb
        exact ⟨t, ht, hb, by rw [← e1]; exact h1, by rw [← e2]; exact h2⟩
    · have hset : satV e (liftC C ++ [(g1, 1), (g2, 1)]) =
          {z | (fun i => z (Fin.castSucc i)) ∈ satV e C ∧
            φ.evalV e (fun i => z (Fin.castSucc i)) < z (Fin.last n) ∧
            z (Fin.last n) < ψ.evalV e (fun i => z (Fin.castSucc i))} := by
        ext z
        rw [mem_satV_liftC_append, List.forall_mem_cons, List.forall_mem_singleton]
        show _ ∧ SignType.sign (g1.evalV e z) = 1 ∧ SignType.sign (g2.evalV e z) = 1 ↔ _ ∧ _ ∧ _
        rw [AffFun.evalV_sub, AffFun.evalV_sub, AffFun.evalV_lastFun, AffFun.evalV_liftFun,
          AffFun.evalV_liftFun, sign_eq_one_iff, sign_eq_one_iff, sub_pos, sub_pos]
      rw [hset]
      refine VCell.band hcell φ ψ fun z hz => ?_
      obtain ⟨x, hx⟩ := exists_rat_signs he n ((ψ.sub φ) :: C.map Prod.fst) z
      have hxC : x ∈ satQ C := fun p hp => by
        rw [hx p.1 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)), hz p hp]
      have h0 := hx (ψ.sub φ) List.mem_cons_self
      rw [AffFun.eval_sub, AffFun.evalV_sub, sign_pos (sub_pos.mpr (hltQ x hxC)), eq_comm,
        sign_eq_one_iff, sub_pos] at h0
      exact h0

/-! ### Partition of a realization into cells -/

/-- **Cells of a realization.** If `D ⊆ ℚⁿ` is a bounded union of sign classes of the functions in
`G`, the union of the corresponding sign classes in `Vⁿ` is partitioned into cells, one for each
simplex of a triangulation of `D`, of the same dimension. -/
theorem exists_vcell_partition {e : V} (he : 0 < e) {n : ℕ} (G : List (AffFun n)) {N : ℚ}
    (hN : 0 ≤ N) (D : Set (Fin n → ℚ)) (hsub : D ⊆ box n N) (hD : Constructible G D) :
    ∃ T : Triangulation n D, ∃ C : T.κ → Set (Fin n → V),
      (∀ k, VCell e n (T.dim k) (C k)) ∧ (∀ k k', k ≠ k' → Disjoint (C k) (C k')) ∧
        (⋃ k, C k) = realV e G D := by
  classical
  obtain ⟨T, -, hTc⟩ := exists_triangulation_of_constructible G N hN D hsub hD
  choose L hL hcell using fun k => cyl_realization he (hTc k)
  refine ⟨T, fun k => satV e (L k), hcell, ?_, ?_⟩
  · intro k k' hkk'
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨x, hx⟩ := exists_rat_signs he n ((L k).map Prod.fst ++ (L k').map Prod.fst) z
    have h1 : x ∈ satQ (L k) := fun p hp => by
      rw [hx p.1 (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)), hz p hp]
    have h2 : x ∈ satQ (L k') := fun p hp => by
      rw [hx p.1 (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)), hz' p hp]
    rw [← hL] at h1 h2
    exact Set.disjoint_left.mp (T.disjoint k k' hkk') h1 h2
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, hx⟩ := exists_rat_signs he n (G ++ (L k).map Prod.fst) z
      have hxk : x ∈ satQ (L k) := fun p hp => by
        rw [hx p.1 (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)), hk p hp]
      rw [← hL] at hxk
      have hxD : x ∈ D := by rw [← T.cover]; exact Set.mem_iUnion.mpr ⟨k, hxk⟩
      exact ⟨x, hxD, fun g hg => hx g (List.mem_append_left _ hg)⟩
    · intro z hz
      let all : List (AffFun n) :=
        G ++ (Finset.univ.toList : List T.κ).flatMap fun k => (L k).map Prod.fst
      obtain ⟨x, hx⟩ := exists_rat_signs he n all z
      have hxD : x ∈ D := (mem_realV_iff hD fun g hg => hx g (List.mem_append_left _ hg)).mp hz
      rw [← T.cover] at hxD
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxD
      rw [hL] at hk
      refine Set.mem_iUnion.mpr ⟨k, fun p hp => ?_⟩
      rw [← hx p.1 (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), List.mem_map.mpr ⟨p, hp, rfl⟩⟩)), hk p hp]

end DiamondIntegral.Section8.Prism
