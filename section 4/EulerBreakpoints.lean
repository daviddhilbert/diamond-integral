module

public import «section 4».EulerPointwise

/-! The finite canonical set of breakpoints is intrinsic to the actual
function: it consists precisely of the points where the function is not
constant on any open neighbourhood. This will control base provenance. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ]

def ConstantNear (f : Γ → ℤ) (a : Γ) : Prop :=
  ∃ l u, l < a ∧ a < u ∧ ∀ x, l < x → x < u → f x = f a

theorem stepEval_constantNear_iff (v : StepCoefficients Γ) (a : Γ) :
    ConstantNear (stepEval v) a ↔ v.2.1 a = 0 ∧ v.2.2 a = 0 := by
  let S := v.2.1.support ∪ v.2.2.support
  constructor
  · rintro ⟨l, u, hla, hau, hconst⟩
    obtain ⟨x, hxa, hx⟩ := exists_left_gap (insert l S) a
    obtain ⟨y, hay, hy⟩ := exists_right_gap (insert u S) a
    have hlx : l < x := hx l (Finset.mem_insert_self _ _) hla
    have hyu : y < u := hy u (Finset.mem_insert_self _ _) hau
    have hpx : v.2.1 x = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro h
      exact (lt_irrefl x) (hx x
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)) hxa)
    have hpy : v.2.1 y = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro h
      exact (lt_irrefl y) (hy y
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)) hay)
    have hprex := jumpPrefix_left v.2.2 x a hxa
      (fun b hb hba => hx b (Finset.mem_insert_of_mem (Finset.mem_union_right _ hb)) hba)
    have hprey := jumpPrefix_right v.2.2 a y hay
      (fun b hb hab => hy b (Finset.mem_insert_of_mem (Finset.mem_union_right _ hb)) hab)
    have ex := hconst x hlx (hxa.trans hau)
    have ey := hconst y (hla.trans hay) hyu
    simp only [stepEval, hpx, hpy, hprex, hprey] at ex ey
    constructor <;> omega
  · rintro ⟨hp, hq⟩
    obtain ⟨l, hla, hl⟩ := exists_left_gap S a
    obtain ⟨u, hau, hu⟩ := exists_right_gap S a
    refine ⟨l, u, hla, hau, ?_⟩
    intro x hlx hxu
    rcases lt_trichotomy x a with hxa | hxa | hax
    · have hpx : v.2.1 x = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro h
        exact (not_lt_of_ge (hl x (Finset.mem_union_left _ h) hxa).le) hlx
      have hprex := jumpPrefix_left v.2.2 x a hxa
        (fun b hb hba => (hl b (Finset.mem_union_right _ hb) hba).trans hlx)
      simp only [stepEval, hpx, hp, hprex]
    · subst x
      rfl
    · have hpx : v.2.1 x = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro h
        exact (not_lt_of_ge (hu x (Finset.mem_union_left _ h) hax).le) hxu
      have hprex := jumpPrefix_right v.2.2 a x hax
        (fun b hb hab => hxu.trans (hu b (Finset.mem_union_right _ hb) hab))
      simp only [stepEval, hpx, hp, hq, hprex, add_zero]

theorem stepEval_breakpoints (v : StepCoefficients Γ) :
    {a | ¬ ConstantNear (stepEval v) a} =
      (v.2.1.support ∪ v.2.2.support : Finset Γ) := by
  ext a
  simp only [Set.mem_ofPred_eq, stepEval_constantNear_iff, Finset.mem_coe,
    Finset.mem_union, Finsupp.mem_support_iff, not_and_or]

theorem stepEval_finite_breakpoints (v : StepCoefficients Γ) :
    {a | ¬ ConstantNear (stepEval v) a}.Finite := by
  rw [stepEval_breakpoints]
  exact Finset.finite_toSet _

namespace EulerFunction
variable [AddCommGroup Γ]

def breakpoints (k : EulerKind) (f : EulerFunction k Γ) : Finset Γ :=
  ((coefficientEquiv k).symm f).2.1.support ∪ ((coefficientEquiv k).symm f).2.2.support

theorem mem_breakpoints_iff (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    a ∈ breakpoints k f ↔ ¬ ConstantNear f a := by
  have he : stepEval ((coefficientEquiv k).symm f) = (f : Γ → ℤ) :=
    funext (coefficients_eval k f)
  rw [← he]
  exact (Set.ext_iff.mp (stepEval_breakpoints ((coefficientEquiv k).symm f)) a).symm

theorem finite_breakpoints (k : EulerKind) (f : EulerFunction k Γ) :
    {a | ¬ ConstantNear f a}.Finite := by
  have he : stepEval ((coefficientEquiv k).symm f) = (f : Γ → ℤ) :=
    funext (coefficients_eval k f)
  rw [← he]
  exact stepEval_finite_breakpoints _

end EulerFunction
end DiamondIntegral.Section4
