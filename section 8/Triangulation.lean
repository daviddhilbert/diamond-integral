import «section 8».PrismTriangulation

/-! Triangulation of bounded rational polyhedral sets, and Lemma 8.5.2 of
Hrushovski–Loeser over `ℚ`.

`exists_adapted_triangulation`: for finitely many affine functions on `ℚⁿ` the
box `[−N, N]ⁿ` has a triangulation on whose simplices every function has
constant sign. Hence every bounded set that is a union of sign classes is
triangulated (`exists_triangulation_of_constructible`).

`hasLimit_latticeSeries`: for such a set `D` and a weight that is integral
linear in `(x, m)` on each piece of a finite cover by unions of sign classes,
the lattice-point series of `D` lies in `R[T]†`, has degree `≤ 0`, and its
limit is `−χ(D)`, where `χ(D) = ∑_σ (−1)^(dim σ)` for any triangulation of `D`
(`eulerChar_eq`: the sum does not depend on the triangulation).

The file uses Mathlib only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.Prism

open SimplexSeries HeightChains RationalSeries

/-- An affine function on `ℚⁿ` with rational coefficients. -/
structure AffFun (n : ℕ) where
  /-- The linear coefficients. -/
  coeff : Fin n → ℚ
  /-- The constant term. -/
  const : ℚ

namespace AffFun

variable {n : ℕ}

/-- The value at a point. -/
def eval (g : AffFun n) (x : Fin n → ℚ) : ℚ := ∑ i, g.coeff i * x i + g.const

/-- A constant function. -/
def constFun (n : ℕ) (a : ℚ) : AffFun n := ⟨fun _ => 0, a⟩

/-- The difference of two affine functions. -/
def sub (g h : AffFun n) : AffFun n := ⟨fun i => g.coeff i - h.coeff i, g.const - h.const⟩

theorem eval_const (a : ℚ) (x : Fin n → ℚ) : (constFun n a).eval x = a := by
  simp [eval, constFun]

theorem eval_sub (g h : AffFun n) (x : Fin n → ℚ) : (g.sub h).eval x = g.eval x - h.eval x := by
  simp only [eval, sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The part of a function on `ℚⁿ⁺¹` that does not involve the last coordinate. -/
def base (g : AffFun (n + 1)) : AffFun n := ⟨fun i => g.coeff (Fin.castSucc i), g.const⟩

/-- The coefficient of the last coordinate. -/
def lead (g : AffFun (n + 1)) : ℚ := g.coeff (Fin.last n)

/-- The function `φ` on `ℚⁿ` with `g(x, y) = lead · (y − φ(x))`. -/
def solve (g : AffFun (n + 1)) : AffFun n :=
  ⟨fun i => -g.coeff (Fin.castSucc i) / g.lead, -g.const / g.lead⟩

theorem eval_eq (g : AffFun (n + 1)) (z : Fin (n + 1) → ℚ) :
    g.eval z = g.base.eval (fun i => z (Fin.castSucc i)) + g.lead * z (Fin.last n) := by
  simp only [eval, base, lead, Fin.sum_univ_castSucc]
  ring

theorem eval_eq_solve (g : AffFun (n + 1)) (h : g.lead ≠ 0) (z : Fin (n + 1) → ℚ) :
    g.eval z = g.lead * (z (Fin.last n) - g.solve.eval (fun i => z (Fin.castSucc i))) := by
  have hs : g.solve.eval (fun i => z (Fin.castSucc i)) =
      -(g.base.eval (fun i => z (Fin.castSucc i))) / g.lead := by
    simp only [eval, solve, base]
    have hterm : ∀ i : Fin n, -g.coeff (Fin.castSucc i) / g.lead * z (Fin.castSucc i) =
        -(g.coeff (Fin.castSucc i) * z (Fin.castSucc i)) / g.lead := fun i => by ring
    simp only [hterm]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    ring
  rw [eval_eq, hs]
  field_simp
  ring

theorem eval_bary {ι : Type*} [Fintype ι] (g : AffFun n) (v : ι → Fin n → ℚ) {t : ι → ℚ}
    (ht : IsBary t) {x : Fin n → ℚ} (hx : ∀ i, x i = ∑ j, t j * v j i) :
    g.eval x = ev t (fun j => g.eval (v j)) := by
  have h1 : ∑ i, g.coeff i * x i = ∑ j, t j * ∑ i, g.coeff i * v j i := by
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  simp only [eval, ev, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht.2, one_mul]
  rw [h1]

end AffFun

variable {n : ℕ}

/-- Every function of the list has constant sign on every simplex. -/
def Triangulation.Adapted {D : Set (Fin n → ℚ)} (T : Triangulation n D) (G : List (AffFun n)) :
    Prop :=
  ∀ k, ∀ g ∈ G, ∀ x ∈ openSimplex (T.vert k), ∀ y ∈ openSimplex (T.vert k),
    SignType.sign (g.eval x) = SignType.sign (g.eval y)

/-- The triangulation of `ℚ⁰` by its point. -/
noncomputable def pointTriangulation (N : ℚ) : Triangulation 0 (box 0 N) where
  κ := Unit
  dim := fun _ => 0
  vert := fun _ _ => 0
  indep := fun _ => by
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    exact affineIndependent_of_subsingleton ℚ _
  disjoint := fun k k' h => absurd (Subsingleton.elim k k') h
  cover := by
    ext x
    simp only [Set.mem_iUnion, box]
    constructor
    · intro _ i
      exact i.elim0
    · intro _
      exact ⟨(), fun _ => 1, fun _ => one_pos, by simp, fun i => i.elim0⟩

/-- **Triangulation.** The box has a triangulation adapted to any finite list of affine
functions. -/
theorem exists_adapted_triangulation (n : ℕ) :
    ∀ (G : List (AffFun n)) (N : ℚ), 0 ≤ N →
      ∃ T : Triangulation n (box n N), T.Adapted G ∧ T.Cyl := by
  induction n with
  | zero =>
    intro G N _
    refine ⟨pointTriangulation N, fun k g _ x _ y _ => ?_, fun _ => IsCyl.point _⟩
    rw [Subsingleton.elim x y]
  | succ n ih =>
    intro G N hN
    let Φ : List (AffFun n) := AffFun.constFun n (-N) :: AffFun.constFun n N ::
      (G.filter fun g => decide (g.lead ≠ 0)).map AffFun.solve
    let G' : List (AffFun n) := (G.filter fun g => decide (g.lead = 0)).map AffFun.base ++
      (Φ ×ˢ Φ).map fun p => p.1.sub p.2
    have hΦlo : AffFun.constFun n (-N) ∈ Φ := List.mem_cons_self
    have hΦhi : AffFun.constFun n N ∈ Φ := List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨T, hT, hTc⟩ := ih G' N hN
    let vals : ∀ k, AffFun n → (Fin (T.dim k + 1) → ℚ) := fun k φ j => φ.eval (T.vert k j)
    have hvconst : ∀ k (a : ℚ), vals k (AffFun.constFun n a) = fun _ => a := fun k a =>
      funext fun j => AffFun.eval_const a _
    have hx : ∀ k (t : Fin (T.dim k + 1) → ℚ), IsBary t →
        (fun i => ∑ j, t j * T.vert k j i) ∈ openSimplex (T.vert k) := fun k t ht =>
      (mem_openSimplex_iff _ _).mpr ⟨t, ht, fun _ => rfl⟩
    have hcmp : ∀ k, ∀ φ ∈ Φ, ∀ φ' ∈ Φ, vals k φ ≤ vals k φ' ∨ vals k φ' ≤ vals k φ := by
      intro k φ hφ φ' hφ'
      have hmem : φ.sub φ' ∈ G' :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(φ, φ'), List.pair_mem_product.mpr ⟨hφ, hφ'⟩, rfl⟩)
      have hsign := hT k _ hmem
      have hev : ∀ t, IsBary t → (φ.sub φ').eval (fun i => ∑ j, t j * T.vert k j i) =
          ev t (vals k φ) - ev t (vals k φ') := fun t ht => by
        rw [AffFun.eval_sub, AffFun.eval_bary φ _ ht fun _ => rfl,
          AffFun.eval_bary φ' _ ht fun _ => rfl]
      have hb := isBary_barycentre (ι := Fin (T.dim k + 1))
      apply comparable_of_sign
      rcases lt_trichotomy (ev _ (vals k φ)) (ev _ (vals k φ')) with h | h | h
      · left
        intro t ht
        have := hsign _ (hx k t ht) _ (hx k _ hb)
        rw [hev t ht, hev _ hb, sign_neg (sub_neg.mpr h), sign_eq_neg_one_iff] at this
        linarith
      · right; left
        intro t ht
        have := hsign _ (hx k t ht) _ (hx k _ hb)
        rw [hev t ht, hev _ hb, h, sub_self, sign_zero, sign_eq_zero_iff] at this
        linarith
      · right; right
        intro t ht
        have := hsign _ (hx k t ht) _ (hx k _ hb)
        rw [hev t ht, hev _ hb, sign_pos (sub_pos.mpr h), sign_eq_one_iff] at this
        linarith
    classical
    let V : ∀ k, Finset (Fin (T.dim k + 1) → ℚ) := fun k =>
      (Φ.toFinset.image (vals k)).filter fun u => (fun _ => -N) ≤ u ∧ u ≤ fun _ => N
    have hVchain : ∀ k, IsChainF (V k) := by
      intro k u hu u' hu'
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      obtain ⟨φ', hφ', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu').1
      exact hcmp k φ (List.mem_toFinset.mp hφ) φ' (List.mem_toFinset.mp hφ')
    choose W hVW hWchain hWelem hWbd using fun k =>
      exists_elementary_refinement (V k) (hVchain k)
    have hloV : ∀ k, (fun _ => -N) ∈ V k := fun k =>
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨_, List.mem_toFinset.mpr hΦlo, hvconst k (-N)⟩, le_rfl, fun _ => by show -N ≤ N; linarith⟩
    have hhiV : ∀ k, (fun _ => N) ∈ V k := fun k =>
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨_, List.mem_toFinset.mpr hΦhi, hvconst k N⟩, fun _ => by show -N ≤ N; linarith, le_rfl⟩
    have hbd : ∀ k, ∀ w ∈ W k, (fun _ => -N) ≤ w ∧ w ≤ fun _ => N := by
      intro k w hw
      obtain ⟨f, hf, g, hg, h1, h2⟩ := hWbd k w hw
      exact ⟨(Finset.mem_filter.mp hf).2.1.trans h1, h2.trans (Finset.mem_filter.mp hg).2.2⟩
    refine ⟨prism T W hWchain hWelem (fun k => hVW k (hloV k)) (fun k => hVW k (hhiV k)) hbd, ?_,
      prism_cyl T W hWchain hWelem _ _ hbd hTc⟩
    rintro ⟨k, a⟩ g hg z hz z' hz'
    have hz1 : z ∈ pieceSet T W k a := hz
    have hz1' : z' ∈ pieceSet T W k a := hz'
    have hzb := piece_over_base T W k a hz1
    have hzb' := piece_over_base T W k a hz1'
    by_cases hlead : g.lead = 0
    · rw [AffFun.eval_eq, AffFun.eval_eq, hlead, zero_mul, zero_mul, add_zero, add_zero]
      exact hT k g.base (List.mem_append_left _ (List.mem_map.mpr
        ⟨g, List.mem_filter.mpr ⟨hg, by simpa using hlead⟩, rfl⟩)) _ hzb _ hzb'
    · rw [AffFun.eval_eq_solve g hlead, AffFun.eval_eq_solve g hlead, sign_mul, sign_mul]
      congr 1
      have hφ : g.solve ∈ Φ := List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, by simpa using hlead⟩, rfl⟩))
      have hu : vals k g.solve ∈ W k ∨ vals k g.solve ≤ (fun _ => -N) ∨
          (fun _ => N) ≤ vals k g.solve := by
        by_cases h1 : (fun _ => -N) ≤ vals k g.solve
        · by_cases h2 : vals k g.solve ≤ fun _ => N
          · exact Or.inl (hVW k (Finset.mem_filter.mpr
              ⟨Finset.mem_image.mpr ⟨g.solve, List.mem_toFinset.mpr hφ, rfl⟩, h1, h2⟩))
          · right; right
            rcases hcmp k g.solve hφ _ hΦhi with h | h
            · rw [hvconst k N] at h
              exact absurd h h2
            · rw [hvconst k N] at h
              exact h
        · right; left
          rcases hcmp k _ hΦlo g.solve hφ with h | h
          · rw [hvconst k (-N)] at h
            exact absurd h h1
          · rw [hvconst k (-N)] at h
            exact h
      obtain ⟨s, hs⟩ := sign_const_on_piece T W hWchain hbd k a (vals k g.solve) hu
      obtain ⟨t, ht, hb⟩ := (mem_openSimplex_iff _ _).mp hzb
      obtain ⟨t', ht', hb'⟩ := (mem_openSimplex_iff _ _).mp hzb'
      rw [AffFun.eval_bary g.solve (T.vert k) ht hb, AffFun.eval_bary g.solve (T.vert k) ht' hb']
      exact (hs z hz1 t ht hb).trans (hs z' hz1' t' ht' hb').symm

/-! ### Unions of sign classes -/

/-- `D` is a union of sign classes of the functions in `G`. -/
def Constructible (G : List (AffFun n)) (D : Set (Fin n → ℚ)) : Prop :=
  ∀ x y, (∀ g ∈ G, SignType.sign (g.eval x) = SignType.sign (g.eval y)) → (x ∈ D ↔ y ∈ D)

theorem Triangulation.subset_or_disjoint {D' D : Set (Fin n → ℚ)} {T : Triangulation n D'}
    {G : List (AffFun n)} (hT : T.Adapted G) (hD : Constructible G D) (k : T.κ) :
    openSimplex (T.vert k) ⊆ D ∨ Disjoint (openSimplex (T.vert k)) D := by
  by_cases h : ∃ x ∈ openSimplex (T.vert k), x ∈ D
  · obtain ⟨x, hx, hxD⟩ := h
    exact Or.inl fun y hy => (hD x y fun g hg => hT k g hg x hx y hy).mp hxD
  · exact Or.inr (Set.disjoint_left.mpr fun x hx hxD => h ⟨x, hx, hxD⟩)

/-- The simplices of a triangulation that lie in `D`. -/
noncomputable def Triangulation.restrict {D' D : Set (Fin n → ℚ)} (T : Triangulation n D')
    (hsub : D ⊆ D')
    (h : ∀ k, openSimplex (T.vert k) ⊆ D ∨ Disjoint (openSimplex (T.vert k)) D) :
    Triangulation n D where
  κ := {k : T.κ // openSimplex (T.vert k) ⊆ D}
  fin := Fintype.ofFinite _
  dim := fun k => T.dim k.1
  vert := fun k => T.vert k.1
  indep := fun k => T.indep k.1
  disjoint := fun k k' hkk' => T.disjoint k.1 k'.1 fun he => hkk' (Subtype.ext he)
  cover := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact k.2 hk
    · intro x hx
      have hx' := hsub hx
      rw [← T.cover] at hx'
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx'
      rcases h k with h1 | h1
      · exact Set.mem_iUnion.mpr ⟨⟨k, h1⟩, hk⟩
      · exact absurd hx (Set.disjoint_left.mp h1 hk)

/-- Every bounded union of sign classes has an adapted triangulation. -/
theorem exists_triangulation_of_constructible (G : List (AffFun n)) (N : ℚ) (hN : 0 ≤ N)
    (D : Set (Fin n → ℚ)) (hsub : D ⊆ box n N) (hD : Constructible G D) :
    ∃ T : Triangulation n D, T.Adapted G ∧ T.Cyl := by
  obtain ⟨T, hT, hTc⟩ := exists_adapted_triangulation n G N hN
  exact ⟨T.restrict hsub fun k => Triangulation.subset_or_disjoint hT hD k,
    fun k g hg x hx y hy => hT k.1 g hg x hx y hy, fun k => hTc k.1⟩

/-! ### The Euler characteristic and Lemma 8.5.2 -/

/-- `∑_σ (−1)^(dim σ)`. -/
def Triangulation.eulerChar {D : Set (Fin n → ℚ)} (T : Triangulation n D) : ℤ :=
  ∑ k, (-1) ^ T.dim k

/-- The lattice-point series of a triangulated set, for a weight that is integral linear on the
cone over each simplex. -/
theorem Triangulation.hasLimit {R : Type*} [CommRing R] (A : Rˣ) {D : Set (Fin n → ℚ)}
    (T : Triangulation n D) (wt : (Fin n → ℤ) → ℕ → ℤ) (a : T.κ → Fin n → ℤ) (b : T.κ → ℤ)
    (hwt : ∀ (k : T.κ) (x : Fin n → ℤ) (m : ℕ),
      (fun i => (x i : ℚ) / m) ∈ openSimplex (T.vert k) → wt x m = ∑ i, a k i * x i + b k * m) :
    HasLimit A (latticeSeries A D wt) (-(T.eulerChar : R)) := by
  have h := hasLimit_of_triangulation A (fun k => Fin (T.dim k + 1)) T.vert T.indep
    (fun k k' hkk' => T.disjoint k k' hkk') a b wt hwt
  rw [T.cover] at h
  have hc : (∑ k, (-1 : R) ^ Fintype.card (Fin (T.dim k + 1))) = -(T.eulerChar : R) := by
    simp only [Fintype.card_fin, Triangulation.eulerChar, pow_succ, mul_neg, mul_one,
      Finset.sum_neg_distrib]
    push_cast
    rfl
  rw [hc] at h
  exact h

/-- The alternating sum does not depend on the triangulation. -/
theorem eulerChar_eq {D : Set (Fin n → ℚ)} (T T' : Triangulation n D) :
    T.eulerChar = T'.eulerChar := by
  have h := T.hasLimit (1 : ℤˣ) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (by intros; simp)
  have h' := T'.hasLimit (1 : ℤˣ) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (by intros; simp)
  have := h.unique (1 : ℤˣ) h'
  simpa using this

/-- **Lemma 8.5.2 of Hrushovski–Loeser, over `ℚ`.** Let `D ⊆ ℚⁿ` be a bounded union of sign
classes of finitely many affine functions, covered by unions of sign classes `P r` on each of
which the weight is `wt x m = a_r · x + b_r m` with integral `a_r`, `b_r`. Then the series
`∑_{m ≥ 1} ∑_{x ∈ ℤⁿ, x/m ∈ D} A^(wt x m) T^m` lies in `R[T]†`, has degree `≤ 0`, and its limit
at infinity is `−χ(D)`, with `χ(D)` computed from any triangulation of `D`. -/
theorem hasLimit_latticeSeries {R : Type*} [CommRing R] (A : Rˣ) (G : List (AffFun n)) {N : ℚ}
    (hN : 0 ≤ N) {D : Set (Fin n → ℚ)} (hsub : D ⊆ box n N) (hD : Constructible G D)
    {ρ : Type*} (P : ρ → Set (Fin n → ℚ)) (hP : ∀ r, Constructible G (P r))
    (hcov : D ⊆ ⋃ r, P r) (a : ρ → Fin n → ℤ) (b : ρ → ℤ) (wt : (Fin n → ℤ) → ℕ → ℤ)
    (hwt : ∀ (r : ρ) (x : Fin n → ℤ) (m : ℕ), (fun i => (x i : ℚ) / m) ∈ D ∩ P r →
      wt x m = ∑ i, a r i * x i + b r * m)
    (T : Triangulation n D) : HasLimit A (latticeSeries A D wt) (-(T.eulerChar : R)) := by
  obtain ⟨T', hT', -⟩ := exists_triangulation_of_constructible G N hN D hsub hD
  rw [eulerChar_eq T T']
  have hmem : ∀ k, openSimplex (T'.vert k) ⊆ D := fun k x hx => by
    rw [← T'.cover]
    exact Set.mem_iUnion.mpr ⟨k, hx⟩
  have hr : ∀ k, ∃ r, openSimplex (T'.vert k) ⊆ P r := by
    intro k
    have hx : (fun i => ∑ j, (1 : ℚ) / Fintype.card (Fin (T'.dim k + 1)) * T'.vert k j i) ∈
        openSimplex (T'.vert k) :=
      (mem_openSimplex_iff _ _).mpr ⟨_, isBary_barycentre, fun _ => rfl⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcov (hmem k hx))
    exact ⟨r, fun y hy => (hP r _ y fun g hg => hT' k g hg _ hx y hy).mp hr⟩
  choose r hr using hr
  exact T'.hasLimit A wt (fun k => a (r k)) (fun k => b (r k)) fun k x m hx =>
    hwt (r k) x m ⟨hmem k hx, hr k hx⟩

end DiamondIntegral.Section8.Prism
