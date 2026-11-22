import «section 8».PrismSimplices
import Mathlib.Basic.Sign.Basic

/-! Triangulating the cylinder over a triangulation.

A `Triangulation n D` is a finite family of pairwise disjoint open simplices
with affinely independent rational vertices whose union is `D ⊆ ℚⁿ`. Given a
triangulation of the box `[−N, N]ⁿ` and, over each simplex, an elementary chain
of height functions between the constants `−N` and `N`, the graphs of the
members of the chains and the bands between consecutive members triangulate
`[−N, N]ⁿ⁺¹`. The file uses Mathlib only. -/

set_option autoImplicit false

namespace DiamondIntegral.Section8.Prism

open SimplexSeries HeightChains

/-- A finite partition of `D` into open simplices with affinely independent vertices. -/
structure Triangulation (n : ℕ) (D : Set (Fin n → ℚ)) where
  /-- The index set of the simplices. -/
  κ : Type
  [fin : Fintype κ]
  /-- The dimension of a simplex. -/
  dim : κ → ℕ
  /-- The vertices of a simplex. -/
  vert : ∀ k, Fin (dim k + 1) → Fin n → ℚ
  indep : ∀ k, AffineIndependent ℚ (vert k)
  disjoint : ∀ k k', k ≠ k' → Disjoint (openSimplex (vert k)) (openSimplex (vert k'))
  cover : (⋃ k, openSimplex (vert k)) = D

attribute [instance] Triangulation.fin

/-- Vertex families of *cylindrical* simplices: the point of `ℚ⁰`, the graph of a height function
over a cylindrical simplex, and an elementary band over a cylindrical simplex. -/
inductive IsCyl : ∀ {n d : ℕ}, (Fin (d + 1) → Fin n → ℚ) → Prop
  | point (v : Fin (0 + 1) → Fin 0 → ℚ) : IsCyl v
  | graph {n d : ℕ} (v : Fin (d + 1) → Fin n → ℚ) (w : Fin (d + 1) → ℚ) :
      IsCyl v → IsCyl (lift v w)
  | band {n d : ℕ} (v : Fin (d + 1) → Fin n → ℚ) (f : Fin (d + 1) → ℚ) (j : Fin (d + 1)) (c : ℚ)
      (h : f j < c) : IsCyl v → @IsCyl (n + 1) (d + 1) (bandVertices v f j c)

/-- All simplices of the triangulation are cylindrical. -/
def Triangulation.Cyl {n : ℕ} {D : Set (Fin n → ℚ)} (T : Triangulation n D) : Prop :=
  ∀ k, IsCyl (T.vert k)

/-- The box `[−N, N]ⁿ`. -/
def box (n : ℕ) (N : ℚ) : Set (Fin n → ℚ) := {x | ∀ i, |x i| ≤ N}

section prism

variable {n : ℕ} {N : ℚ} (T : Triangulation n (box n N))
variable (W : ∀ k, Finset (Fin (T.dim k + 1) → ℚ))

open Classical in
/-- The elementary bands over the simplex `k`: consecutive members `f < g` of the chain and the
vertex `j` at which they differ. -/
noncomputable def Bands (k : T.κ) :
    Finset ((Fin (T.dim k + 1) → ℚ) × (Fin (T.dim k + 1) → ℚ) × Fin (T.dim k + 1)) :=
  ((W k) ×ˢ ((W k) ×ˢ Finset.univ)).filter fun p =>
    Consec (W k) p.1 p.2.1 ∧ ∀ i, i ≠ p.2.2 → p.1 i = p.2.1 i

theorem mem_Bands {k : T.κ}
    {p : (Fin (T.dim k + 1) → ℚ) × (Fin (T.dim k + 1) → ℚ) × Fin (T.dim k + 1)} :
    p ∈ Bands T W k ↔ Consec (W k) p.1 p.2.1 ∧ ∀ i, i ≠ p.2.2 → p.1 i = p.2.1 i := by
  classical
  simp only [Bands, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.1.2.1⟩, h⟩⟩

theorem lt_at_of_mem_Bands {k : T.κ}
    {p : (Fin (T.dim k + 1) → ℚ) × (Fin (T.dim k + 1) → ℚ) × Fin (T.dim k + 1)}
    (hp : p ∈ Bands T W k) : p.1 p.2.2 < p.2.1 p.2.2 := by
  obtain ⟨hc, hoff⟩ := (mem_Bands T W).mp hp
  obtain ⟨-, i, hi⟩ := Pi.lt_def.mp hc.2.2.1
  by_cases hij : i = p.2.2
  · rw [← hij]; exact hi
  · exact absurd (hoff i hij) hi.ne

/-- The pieces over the simplex `k`: graphs and elementary bands. -/
abbrev PieceIdx (k : T.κ) := {w // w ∈ W k} ⊕ {p // p ∈ Bands T W k}

/-- The dimension of a piece. -/
def pieceDim (k : T.κ) : PieceIdx T W k → ℕ
  | .inl _ => T.dim k
  | .inr _ => T.dim k + 1

/-- The vertices of a piece. -/
def pieceVert (k : T.κ) : (a : PieceIdx T W k) → Fin (pieceDim T W k a + 1) → Fin (n + 1) → ℚ
  | .inl w => lift (T.vert k) w.1
  | .inr p => bandVertices (T.vert k) p.1.1 p.1.2.2 (p.1.2.1 p.1.2.2)

/-- A piece as a set. -/
def pieceSet (k : T.κ) (a : PieceIdx T W k) : Set (Fin (n + 1) → ℚ) :=
  openSimplex (pieceVert T W k a)

theorem pieceSet_inl (k : T.κ) (w : {w // w ∈ W k}) :
    pieceSet T W k (.inl w) = openSimplex (lift (T.vert k) w.1) := rfl

theorem pieceSet_inr (k : T.κ) (p : {p // p ∈ Bands T W k}) :
    pieceSet T W k (.inr p) = band (T.vert k) p.1.1 p.1.2.1 :=
  (band_eq_simplex (T.vert k) ((mem_Bands T W).mp p.2).2 (lt_at_of_mem_Bands T W p.2)).symm

theorem isCyl_piece (hT : T.Cyl) (k : T.κ) (a : PieceIdx T W k) : IsCyl (pieceVert T W k a) := by
  rcases a with w | p
  · exact IsCyl.graph _ _ (hT k)
  · exact IsCyl.band _ _ _ _ (lt_at_of_mem_Bands T W p.2) (hT k)

theorem piece_over_base (k : T.κ) (a : PieceIdx T W k) {z : Fin (n + 1) → ℚ}
    (hz : z ∈ pieceSet T W k a) : (fun i => z (Fin.castSucc i)) ∈ openSimplex (T.vert k) := by
  rcases a with w | p
  · exact graph_over_base hz
  · rw [pieceSet_inr] at hz
    exact band_over_base hz

theorem indep_piece (k : T.κ) (a : PieceIdx T W k) :
    AffineIndependent ℚ (pieceVert T W k a) := by
  rcases a with w | p
  · exact indep_lift (T.indep k) w.1
  · exact indep_band (T.indep k) _ _ (lt_at_of_mem_Bands T W p.2).ne'

section hypotheses

variable (hchain : ∀ k, IsChainF (W k)) (helem : ∀ k, Elementary (W k))
variable (hlo : ∀ k, (fun _ => -N) ∈ W k) (hhi : ∀ k, (fun _ => N) ∈ W k)
variable (hbd : ∀ k, ∀ w ∈ W k, (fun _ => -N) ≤ w ∧ w ≤ fun _ => N)

include hbd in
theorem piece_subset_cyl (k : T.κ) (a : PieceIdx T W k) :
    pieceSet T W k a ⊆ cyl (T.vert k) (fun _ => -N) (fun _ => N) := by
  rcases a with w | p
  · exact graph_subset_cyl (hbd k w.1 w.2).1 (hbd k w.1 w.2).2
  · rw [pieceSet_inr]
    have hc := ((mem_Bands T W).mp p.2).1
    exact band_subset_cyl (hbd k _ hc.1).1 (hbd k _ hc.2.1).2

theorem cyl_subset_box (k : T.κ) :
    cyl (T.vert k) (fun _ => -N) (fun _ => N) ⊆ box (n + 1) N := by
  rintro z ⟨t, ht, hb, h1, h2⟩
  rw [ev_const ht] at h1 h2
  have hbase : (fun i => z (Fin.castSucc i)) ∈ box n N := by
    rw [← T.cover]
    exact Set.mem_iUnion.mpr ⟨k, (mem_openSimplex_iff _ _).mpr ⟨t, ht, hb⟩⟩
  show ∀ c, |z c| ≤ N
  rw [Fin.forall_fin_succ']
  exact ⟨fun i => hbase i, abs_le.mpr ⟨h1, h2⟩⟩

include hchain in
theorem piece_disjoint (k : T.κ) (a a' : PieceIdx T W k) (ha : a ≠ a') :
    Disjoint (pieceSet T W k a) (pieceSet T W k a') := by
  rcases a with w | p <;> rcases a' with w' | p'
  · exact graph_disjoint (T.indep k) (hchain k) w.2 w'.2
      fun h => ha (congrArg Sum.inl (Subtype.ext h))
  · rw [pieceSet_inr]
    exact graph_band_disjoint (T.indep k) (hchain k) w.2 ((mem_Bands T W).mp p'.2).1
  · rw [pieceSet_inr]
    exact (graph_band_disjoint (T.indep k) (hchain k) w'.2 ((mem_Bands T W).mp p.2).1).symm
  · rw [pieceSet_inr, pieceSet_inr]
    refine band_disjoint (T.indep k) (hchain k) ((mem_Bands T W).mp p.2).1
      ((mem_Bands T W).mp p'.2).1 fun ⟨h1, h2⟩ => ha ?_
    have hj : p.1.2.2 = p'.1.2.2 := by
      by_contra hjne
      have hlt := lt_at_of_mem_Bands T W p.2
      have hoff := ((mem_Bands T W).mp p'.2).2 p.1.2.2 hjne
      rw [← h1, ← h2] at hoff
      exact hlt.ne hoff
    exact congrArg Sum.inr (Subtype.ext (Prod.ext h1 (Prod.ext h2 hj)))

include hchain helem hlo hhi hbd in
/-- The triangulation of `[−N, N]ⁿ⁺¹` by graphs and elementary bands. -/
noncomputable def prism : Triangulation (n + 1) (box (n + 1) N) where
  κ := Σ k : T.κ, PieceIdx T W k
  dim := fun x => pieceDim T W x.1 x.2
  vert := fun x => pieceVert T W x.1 x.2
  indep := fun x => indep_piece T W x.1 x.2
  disjoint := by
    rintro ⟨k, a⟩ ⟨k', a'⟩ hne
    by_cases hk : k = k'
    · subst hk
      exact piece_disjoint T W hchain k a a' fun h => hne (by rw [h])
    · rw [Set.disjoint_left]
      intro z hz hz'
      exact Set.disjoint_left.mp (T.disjoint k k' hk) (piece_over_base T W k a hz)
        (piece_over_base T W k' a' hz')
  cover := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨⟨k, a⟩, hz⟩ := Set.mem_iUnion.mp hz
      exact cyl_subset_box T k (piece_subset_cyl T W hbd k a hz)
    · intro z hz
      have hbase : (fun i => z (Fin.castSucc i)) ∈ box n N := fun i => hz (Fin.castSucc i)
      rw [← T.cover] at hbase
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hbase
      obtain ⟨t, ht, hb⟩ := (mem_openSimplex_iff _ _).mp hk
      have hcyl : z ∈ cyl (T.vert k) (fun _ => -N) (fun _ => N) :=
        ⟨t, ht, hb, by rw [ev_const ht]; exact (abs_le.mp (hz (Fin.last n))).1,
          by rw [ev_const ht]; exact (abs_le.mp (hz (Fin.last n))).2⟩
      rcases cyl_cases (hchain k) (hlo k) (hhi k) hcyl with ⟨w, hw, hzw⟩ | ⟨f, g, hc, hzb⟩
      · exact Set.mem_iUnion.mpr ⟨⟨k, .inl ⟨w, hw⟩⟩, hzw⟩
      · obtain ⟨j, hj⟩ := helem k f g hc
        have hp : (f, g, j) ∈ Bands T W k := (mem_Bands T W).mpr ⟨hc, hj⟩
        refine Set.mem_iUnion.mpr ⟨⟨k, .inr ⟨(f, g, j), hp⟩⟩, ?_⟩
        show z ∈ pieceSet T W k (.inr ⟨(f, g, j), hp⟩)
        rw [pieceSet_inr]
        exact hzb

include hchain helem hlo hhi hbd in
theorem prism_cyl (hT : T.Cyl) : (prism T W hchain helem hlo hhi hbd).Cyl :=
  fun x => isCyl_piece T W hT x.1 x.2

include hchain hbd in
/-- A height function that belongs to the chain, or lies below `−N` or above `N`, has
constant position relative to each piece. -/
theorem sign_const_on_piece (k : T.κ) (a : PieceIdx T W k) (u : Fin (T.dim k + 1) → ℚ)
    (hu : u ∈ W k ∨ u ≤ (fun _ => -N) ∨ (fun _ => N) ≤ u) :
    ∃ s : SignType, ∀ z ∈ pieceSet T W k a, ∀ t, IsBary t → OverBase (T.vert k) t z →
      SignType.sign (z (Fin.last n) - ev t u) = s := by
  have hcmp : ∀ w ∈ W k, w ≤ u ∨ u ≤ w := by
    intro w hw
    rcases hu with hu | hu | hu
    · exact hchain k w hw u hu
    · exact Or.inr (hu.trans (hbd k w hw).1)
    · exact Or.inl ((hbd k w hw).2.trans hu)
  rcases a with w | p
  · have key : ∀ z ∈ pieceSet T W k (.inl w), ∀ t, IsBary t → OverBase (T.vert k) t z →
        z (Fin.last n) = ev t w.1 := by
      intro z hz t ht hb
      obtain ⟨t', ht', hb', he⟩ := (mem_graph_iff (T.vert k) w.1 z).mp hz
      rw [bary_unique (T.indep k) ht ht' hb hb']
      exact he
    by_cases heq : w.1 = u
    · refine ⟨0, fun z hz t ht hb => ?_⟩
      rw [key z hz t ht hb, heq, sub_self, sign_zero]
    · rcases hcmp w.1 w.2 with h | h
      · refine ⟨-1, fun z hz t ht hb => ?_⟩
        rw [key z hz t ht hb]
        exact sign_neg (sub_neg.mpr (ev_strictMono ht (lt_of_le_of_ne h heq)))
      · refine ⟨1, fun z hz t ht hb => ?_⟩
        rw [key z hz t ht hb]
        exact sign_pos (sub_pos.mpr (ev_strictMono ht (lt_of_le_of_ne h (Ne.symm heq))))
  · have hc := ((mem_Bands T W).mp p.2).1
    have key : ∀ z ∈ pieceSet T W k (.inr p), ∀ t, IsBary t → OverBase (T.vert k) t z →
        ev t p.1.1 < z (Fin.last n) ∧ z (Fin.last n) < ev t p.1.2.1 := by
      intro z hz t ht hb
      rw [pieceSet_inr] at hz
      obtain ⟨t', ht', hb', h1, h2⟩ := hz
      rw [bary_unique (T.indep k) ht ht' hb hb']
      exact ⟨h1, h2⟩
    by_cases h1 : u ≤ p.1.1
    · refine ⟨1, fun z hz t ht hb => ?_⟩
      have := (key z hz t ht hb).1
      exact sign_pos (sub_pos.mpr ((ev_mono ht h1).trans_lt this))
    by_cases h2 : p.1.2.1 ≤ u
    · refine ⟨-1, fun z hz t ht hb => ?_⟩
      have := (key z hz t ht hb).2
      exact sign_neg (sub_neg.mpr (this.trans_le (ev_mono ht h2)))
    exfalso
    rcases hu with hu | hu | hu
    · have hfu : p.1.1 < u := by
        rcases hchain k _ hc.1 u hu with h | h
        · exact lt_of_le_of_ne h fun he => h1 (he ▸ le_rfl)
        · exact absurd h h1
      have hug : u < p.1.2.1 := by
        rcases hchain k u hu _ hc.2.1 with h | h
        · exact lt_of_le_of_ne h fun he => h2 (he ▸ le_rfl)
        · exact absurd h h2
      exact hc.2.2.2 u hu ⟨hfu, hug⟩
    · exact h1 (hu.trans (hbd k _ hc.1).1)
    · exact h2 ((hbd k _ hc.2.1).2.trans hu)

end hypotheses

end prism

end DiamondIntegral.Section8.Prism
