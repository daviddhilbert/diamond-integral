module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.DenselyOrdered
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Tactic.Linarith

/-! Actual integer-valued functions with finitely many jumps. These are the
unary generators used in §4. They are not yet identified here with all
first-order definable Gamma functions. No Euler or HK theorem is assumed. -/

@[expose] public noncomputable section
open Classical Finset

namespace DiamondIntegral.Section4

variable {Γ : Type*} [LinearOrder Γ]

def jumpPrefix (q : Γ →₀ ℤ) (x : Γ) : ℤ :=
  q.sum fun a n => if a < x then n else 0

abbrev StepCoefficients (Γ : Type*) := ℤ × (Γ →₀ ℤ) × (Γ →₀ ℤ)

def stepEval (v : StepCoefficients Γ) (x : Γ) : ℤ :=
  v.1 + v.2.1 x + jumpPrefix v.2.2 x

theorem jumpPrefix_zero (x : Γ) : jumpPrefix (0 : Γ →₀ ℤ) x = 0 := by
  simp [jumpPrefix]

theorem jumpPrefix_add (p q : Γ →₀ ℤ) (x : Γ) :
    jumpPrefix (p + q) x = jumpPrefix p x + jumpPrefix q x := by
  apply Finsupp.sum_add_index
  · intro a ha; simp
  · intro a ha m n; split_ifs <;> simp

theorem jumpPrefix_single (a x : Γ) (n : ℤ) :
    jumpPrefix (Finsupp.single a n) x = if a < x then n else 0 := by
  apply Finsupp.sum_single_index
  simp

theorem stepEval_zero : stepEval (0 : StepCoefficients Γ) = 0 := by
  funext x
  simp [stepEval, jumpPrefix_zero]

theorem stepEval_add (u v : StepCoefficients Γ) :
    stepEval (u + v) = stepEval u + stepEval v := by
  funext x
  change (u.1 + v.1) + (u.2.1 x + v.2.1 x) + jumpPrefix (u.2.2 + v.2.2) x = _
  rw [jumpPrefix_add]
  simp only [Pi.add_apply, stepEval]
  omega

def stepEvaluation : StepCoefficients Γ →+ (Γ → ℤ) where
  toFun := stepEval
  map_zero' := stepEval_zero
  map_add' := stepEval_add

theorem jumpPrefix_finite_range (q : Γ →₀ ℤ) : (Set.range (jumpPrefix q)).Finite := by
  have hf := q.support.powerset.finite_toSet.image (fun s : Finset Γ => ∑ a ∈ s, q a)
  apply hf.subset
  rintro z ⟨x, rfl⟩
  refine ⟨q.support.filter (· < x), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  simp only [Finset.sum_filter, jumpPrefix, Finsupp.sum]

theorem stepEval_finite_range (v : StepCoefficients Γ) : (Set.range (stepEval v)).Finite := by
  have hf := Set.Finite.image2 (fun p q : ℤ => v.1 + p + q)
    v.2.1.finite_range (jumpPrefix_finite_range v.2.2)
  apply hf.subset
  rintro z ⟨x, rfl⟩
  exact ⟨v.2.1 x, ⟨x, rfl⟩, jumpPrefix v.2.2 x, ⟨x, rfl⟩, rfl⟩

/-- The carrier consists of actual functions, with ordinary pointwise addition. -/
def stepFunctionSubgroup : AddSubgroup (Γ → ℤ) := stepEvaluation.range

abbrev StepFunction (Γ : Type*) [LinearOrder Γ] := ↥(stepFunctionSubgroup (Γ := Γ))

theorem jumpPrefix_left (q : Γ →₀ ℤ) (x a : Γ) (hxa : x < a)
    (hgap : ∀ b ∈ q.support, b < a → b < x) :
    jumpPrefix q x = jumpPrefix q a := by
  unfold jumpPrefix Finsupp.sum
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hba : b < a
  · simp [hba, hgap b hb hba]
  · have hbx : ¬ b < x := fun h => hba (h.trans hxa)
    simp [hba, hbx]

theorem jumpPrefix_right (q : Γ →₀ ℤ) (a y : Γ) (hay : a < y)
    (hgap : ∀ b ∈ q.support, a < b → y < b) :
    jumpPrefix q y = jumpPrefix q a + q a := by
  have hterm : ∀ b ∈ q.support, (if b < y then q b else 0) =
      (if b < a then q b else 0) + (if b = a then q b else 0) := by
    intro b hb
    by_cases hba : b < a
    · simp [hba, hba.trans hay, ne_of_lt hba]
    · by_cases hbeq : b = a
      · subst b; simp [hay]
      · have hab : a < b := (lt_or_gt_of_ne hbeq).resolve_left hba
        have hby : ¬ b < y := not_lt_of_ge (le_of_lt (hgap b hb hab))
        simp [hba, hbeq, hby]
  unfold jumpPrefix Finsupp.sum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  by_cases ha : a ∈ q.support
  · simp [ha]
  · simp [ha, Finsupp.notMem_support_iff.mp ha]

section Dense
variable [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]

theorem exists_left_gap (s : Finset Γ) (a : Γ) :
    ∃ x, x < a ∧ ∀ b ∈ s, b < a → b < x := by
  let : Nonempty Γ := ⟨a⟩
  obtain ⟨x, hx, ha⟩ := (s.filter (· < a)).exists_between' {a} (by
    intro b hb c hc
    have hca : c = a := by simpa using hc
    subst c
    exact (Finset.mem_filter.mp hb).2)
  exact ⟨x, ha a (Finset.mem_singleton_self a),
    fun b hb hba => hx b (Finset.mem_filter.mpr ⟨hb, hba⟩)⟩

theorem exists_right_gap (s : Finset Γ) (a : Γ) :
    ∃ y, a < y ∧ ∀ b ∈ s, a < b → y < b :=
  exists_left_gap (Γ := Γᵒᵈ) s a

/-- Coefficients are recovered from actual neighbouring function values;
no Archimedean hypothesis or chosen cross-section is used. -/
theorem stepEval_eq_zero_iff [Nonempty Γ] (v : StepCoefficients Γ) :
    stepEval v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hpq : ∀ a : Γ, v.2.1 a = 0 ∧ v.2.2 a = 0 := by
      intro a
      let s := v.2.1.support ∪ v.2.2.support
      obtain ⟨x, hxa, hx⟩ := exists_left_gap s a
      obtain ⟨y, hay, hy⟩ := exists_right_gap s a
      have hpx : v.2.1 x = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hm
        exact (lt_irrefl x) (hx x (Finset.mem_union_left _ hm) hxa)
      have hpy : v.2.1 y = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hm
        exact (lt_irrefl y) (hy y (Finset.mem_union_left _ hm) hay)
      have hprex := jumpPrefix_left v.2.2 x a hxa
        (fun b hb hba => hx b (Finset.mem_union_right _ hb) hba)
      have hprey := jumpPrefix_right v.2.2 a y hay
        (fun b hb hab => hy b (Finset.mem_union_right _ hb) hab)
      have ex := congrFun hv x
      have ea := congrFun hv a
      have ey := congrFun hv y
      simp only [stepEval, Pi.zero_apply, hpx, hpy, hprex, hprey] at ex ea ey
      constructor <;> omega
    have hp : v.2.1 = 0 := Finsupp.ext fun a => (hpq a).1
    have hq : v.2.2 = 0 := Finsupp.ext fun a => (hpq a).2
    have hc : v.1 = 0 := by
      have he := congrFun hv (Classical.arbitrary Γ)
      simpa [stepEval, hp, hq, jumpPrefix_zero] using he
    exact Prod.ext hc (Prod.ext hp hq)
  · rintro rfl
    exact stepEval_zero

theorem stepEvaluation_injective [Nonempty Γ] :
    Function.Injective (stepEvaluation (Γ := Γ)) := by
  intro u v huv
  have hz : stepEvaluation (u - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  exact sub_eq_zero.mp ((stepEval_eq_zero_iff (u - v)).mp hz)

def stepCoefficientsEquiv [Nonempty Γ] : StepCoefficients Γ ≃+ StepFunction Γ :=
  AddMonoidHom.ofInjective stepEvaluation_injective

end Dense

theorem stepFunction_finite_range (f : StepFunction Γ) : (Set.range f.val).Finite := by
  obtain ⟨v, hv⟩ := f.property
  exact hv ▸ stepEval_finite_range v

end DiamondIntegral.Section4
