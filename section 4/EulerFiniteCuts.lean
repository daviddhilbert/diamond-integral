module

public import «section 4».EulerReflection
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases

/-! Every actual function determined by finitely many order cuts belongs
to the finite-jump carrier. Finite cut patterns are constructed explicitly;
no representation or Euler theorem is assumed. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def cutCode (a x : Γ) : Fin 3 := if x < a then 0 else if x = a then 1 else 2

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem cutCode_eq_iff (a x y : Γ) :
    cutCode a x = cutCode a y ↔ (x < a ↔ y < a) ∧ (a < x ↔ a < y) := by
  rcases lt_trichotomy x a with hx | hx | hx <;>
    rcases lt_trichotomy y a with hy | hy | hy <;>
    simp [cutCode, hx, hy, ne_of_lt, ne_of_gt, not_lt_of_ge,
      le_of_lt]

def cutIndicator (k : EulerKind) (a : Γ) (j : Fin 3) : EulerFunction k Γ :=
  if j = 0 then leftRay k a else if j = 1 then point k a else ray k a

theorem cutIndicator_eval (k : EulerKind) (a : Γ) (j : Fin 3) (x : Γ) :
    cutIndicator k a j x = if cutCode a x = j then 1 else 0 := by
  rcases lt_trichotomy x a with h | h | h
  · fin_cases j <;> simp [cutIndicator, cutCode, leftRay_eval, point_eval, ray_eval,
      h, not_lt_of_ge (le_of_lt h), ne_of_lt h]
  · subst x
    fin_cases j <;> simp [cutIndicator, cutCode, leftRay_eval, point_eval, ray_eval]
  · fin_cases j <;> simp [cutIndicator, cutCode, leftRay_eval, point_eval, ray_eval,
      h, not_lt_of_ge (le_of_lt h), ne_of_gt h]

def cutCell (k : EulerKind) : (n : ℕ) → (Fin n → Γ) → (Fin n → Fin 3) → EulerFunction k Γ
  | 0, _, _ => line k
  | n + 1, a, σ => pointwiseProduct k (cutIndicator k (a 0) (σ 0))
      (cutCell k n (fun i => a i.succ) (fun i => σ i.succ))

theorem cutCell_eval (k : EulerKind) (n : ℕ) (a : Fin n → Γ) (σ : Fin n → Fin 3) (x : Γ) :
    cutCell k n a σ x = if ∀ i, cutCode (a i) x = σ i then 1 else 0 := by
  induction n with
  | zero => simp [cutCell, line_eval]
  | succ n ih =>
    rw [cutCell, pointwiseProduct_eval, cutIndicator_eval, ih]
    simp only [Fin.forall_fin_succ]
    by_cases h0 : cutCode (a 0) x = σ 0 <;>
      by_cases hs : ∀ i : Fin n, cutCode (a i.succ) x = σ i.succ <;> simp [h0, hs]

def CutDetermined {n : ℕ} (a : Fin n → Γ) (f : Γ → ℤ) : Prop :=
  ∀ x y, (∀ i, cutCode (a i) x = cutCode (a i) y) → f x = f y

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem exists_finite_cuts_of_finite_range (f : Γ → ℤ) (hf : (Set.range f).Finite)
    (hc : ∀ m : ℤ, ∃ E : Finset Γ, ∀ x y,
      (∀ c ∈ E, cutCode c x = cutCode c y) → (f x = m ↔ f y = m)) :
    ∃ n, ∃ a : Fin n → Γ, CutDetermined a f := by
  choose E hE using hc
  let F := hf.toFinset.biUnion E
  let e := (Finset.equivFin F).symm
  refine ⟨F.card, fun i => (e i).val, ?_⟩
  intro x y hxy
  apply ((hE (f x) x y ?_).mp rfl).symm
  intro c hc
  have hcF : c ∈ F := Finset.mem_biUnion.mpr
    ⟨f x, hf.mem_toFinset.mpr ⟨x, rfl⟩, hc⟩
  have hi := hxy (e.symm ⟨c, hcF⟩)
  simpa only [Equiv.apply_symm_apply] using hi

def cutSampleValue {n : ℕ} (a : Fin n → Γ) (f : Γ → ℤ) (σ : Fin n → Fin 3) : ℤ :=
  if h : ∃ x, ∀ i, cutCode (a i) x = σ i then f (Classical.choose h) else 0

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem cutSampleValue_eq {n : ℕ} (a : Fin n → Γ) (f : Γ → ℤ) (hf : CutDetermined a f)
    (σ : Fin n → Fin 3) (x : Γ) (hx : ∀ i, cutCode (a i) x = σ i) :
    cutSampleValue a f σ = f x := by
  have he : ∃ y, ∀ i, cutCode (a i) y = σ i := ⟨x, hx⟩
  rw [cutSampleValue, dite_eq_left he]
  apply hf
  intro i
  exact (Classical.choose_spec he i).trans (hx i).symm

def ofCutFunction (k : EulerKind) {n : ℕ} (a : Fin n → Γ) (f : Γ → ℤ) : EulerFunction k Γ :=
  ∑ σ : Fin n → Fin 3, cutSampleValue a f σ • cutCell k n a σ

theorem eval_finsetSum {ι : Type*} (k : EulerKind) (s : Finset ι)
    (f : ι → EulerFunction k Γ) (x : Γ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := map_sum (evaluation k x) f s

theorem ofCutFunction_eval (k : EulerKind) {n : ℕ} (a : Fin n → Γ)
    (f : Γ → ℤ) (hf : CutDetermined a f) (x : Γ) : ofCutFunction k a f x = f x := by
  have hσ (σ : Fin n → Fin 3) : (∀ i, cutCode (a i) x = σ i) ↔
      σ = fun i => cutCode (a i) x := by
    constructor
    · intro h
      funext i
      exact (h i).symm
    · rintro rfl
      intro i
      rfl
  simp only [ofCutFunction, eval_finsetSum, eval_zsmul, cutCell_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
  simp_rw [hσ]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact cutSampleValue_eq a f hf _ x (fun _ => rfl)

theorem exists_eulerFunction_of_finite_cuts (k : EulerKind) {n : ℕ}
    (a : Fin n → Γ) (f : Γ → ℤ) (hf : CutDetermined a f) :
    ∃ g : EulerFunction k Γ, ∀ x, g x = f x :=
  ⟨ofCutFunction k a f, ofCutFunction_eval k a f hf⟩

theorem finite_range_of_finite_cuts {n : ℕ} (a : Fin n → Γ) (f : Γ → ℤ)
    (hf : CutDetermined a f) : (Set.range f).Finite := by
  obtain ⟨g, hg⟩ := exists_eulerFunction_of_finite_cuts EulerKind.geometric a f hf
  have he : (g : Γ → ℤ) = f := funext hg
  exact he ▸ finite_range EulerKind.geometric g

end DiamondIntegral.Section4.EulerFunction
