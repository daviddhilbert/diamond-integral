import HilbertMathlib.Foundation.Definability.ElementaryNamedDefinableSets

/-! Traces on an elementary substructure commute with projections.

Let `e : M ↪ₑ N` be elementary and `G ⊆ N^{a+b}` definable over `e(c(P))`. If `x ∈ M^a` and some
`y ∈ N^b` has `(e x, y) ∈ G`, then some `y' ∈ M^b` has `(e x, e y') ∈ G` (`trace_exists`). -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.TraceProjection

open Classical FirstOrder FirstOrder.Language
open DiamondIntegral.Section5

variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable (e : M ↪ₑ[L] N) (c : P → M)

/-- The relabelling that turns the last `b` variables into bound variables. -/
def splitVars (a b : ℕ) : P ⊕ Fin (a + b) → (P ⊕ Fin a) ⊕ Fin b :=
  Sum.elim (fun p => Sum.inl (Sum.inl p)) (Fin.addCases (fun i => Sum.inl (Sum.inr i)) Sum.inr)

theorem realize_split {K : Type} [L.Structure K] {a b : ℕ} (φ : L.Formula (P ⊕ Fin (a + b)))
    (v : P → K) (x : Fin a → K) (y : Fin b → K) :
    (BoundedFormula.relabel (splitVars a b) φ).Realize (Sum.elim v x) (y ∘ Fin.cast (Nat.add_zero b)) ↔
      φ.Realize (Sum.elim v (Fin.append x y)) := by
  rw [BoundedFormula.realize_relabel]
  have hv : (Sum.elim (Sum.elim v x) ((y ∘ Fin.cast (Nat.add_zero b)) ∘ Fin.castAdd 0) ∘ splitVars a b) =
      Sum.elim v (Fin.append x y) := by
    funext i
    cases i with
    | inl p => rfl
    | inr k =>
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simp [splitVars, Fin.append_left]
      · simp [splitVars, Fin.append_right]
  have hx : ((y ∘ Fin.cast (Nat.add_zero b)) ∘ Fin.natAdd b : Fin 0 → K) = default := funext fun i => i.elim0
  rw [hv, hx]
  rfl

/-- **Traces commute with projections.** -/
theorem trace_exists {a b : ℕ} {G : Set (Fin (a + b) → N)} (hG : (Set.range (e ∘ c)).Definable L G)
    (x : Fin a → M) (h : ∃ y : Fin b → N, Fin.append (e ∘ x) y ∈ G) :
    ∃ y : Fin b → M, Fin.append (e ∘ x) (e ∘ y) ∈ G := by
  obtain ⟨φ, rfl⟩ := (namedDefinable_iff_actual (c := e ∘ c)).mpr hG
  obtain ⟨y, hy⟩ := h
  have hN : ∃ y : Fin b → N,
      (BoundedFormula.relabel (splitVars a b) φ).Realize (Sum.elim (e ∘ c) (e ∘ x)) (y ∘ Fin.cast (Nat.add_zero b)) :=
    ⟨y, (realize_split φ (e ∘ c) (e ∘ x) y).mpr hy⟩
  have hN' : ∃ y : Fin (b + 0) → N, (BoundedFormula.relabel (splitVars a b) φ).Realize (Sum.elim (e ∘ c) (e ∘ x)) y := by
    obtain ⟨y, hy⟩ := hN
    exact ⟨_, hy⟩
  obtain ⟨y', hy'⟩ := (elementary_namedFormula_exists_row e c (BoundedFormula.relabel (splitVars a b) φ) x).mp hN'
  refine ⟨y' ∘ Fin.cast (Nat.add_zero b).symm, ?_⟩
  have h1 : (BoundedFormula.relabel (splitVars a b) φ).Realize (Sum.elim c x)
      ((y' ∘ Fin.cast (Nat.add_zero b).symm) ∘ Fin.cast (Nat.add_zero b)) := by
    convert hy' using 2
    funext k
    simp
  have h2 := (realize_split φ c x (y' ∘ Fin.cast (Nat.add_zero b).symm)).mp h1
  have h3 := (elementary_namedFormula_mem e c φ (Fin.append x (y' ∘ Fin.cast (Nat.add_zero b).symm))).mpr h2
  have he : e ∘ Fin.append x (y' ∘ Fin.cast (Nat.add_zero b).symm) =
      Fin.append (e ∘ x) (e ∘ (y' ∘ Fin.cast (Nat.add_zero b).symm)) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [Fin.append_left, Fin.append_right]
  rw [he] at h3
  exact h3

end DiamondIntegral.Section8.TraceProjection
