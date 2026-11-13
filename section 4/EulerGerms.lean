module

public import «section 4».EulerBreakpoints
public import «section 4».EulerBoundedSupport

/-! Actual left and right germ values and the far-left value of a unary
finite-jump function. Their neighbourhood characterizations identify the
canonical coefficients using only values of the actual function. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]
  [AddCommGroup Γ]

def leftValue (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) : ℤ :=
  let v := (coefficientEquiv k).symm f
  v.1 + jumpPrefix v.2.2 a

def rightValue (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) : ℤ :=
  leftValue k f a + ((coefficientEquiv k).symm f).2.2 a

def tailValue (k : EulerKind) (f : EulerFunction k Γ) : ℤ := ((coefficientEquiv k).symm f).1

theorem leftValue_germ (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    ∃ l, l < a ∧ ∀ x, l < x → x < a → f x = leftValue k f a := by
  let v := (coefficientEquiv k).symm f
  let S := v.2.1.support ∪ v.2.2.support
  obtain ⟨l, hla, hl⟩ := exists_left_gap S a
  refine ⟨l, hla, ?_⟩
  intro x hlx hxa
  have hp : v.2.1 x = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact (not_lt_of_ge (hl x (Finset.mem_union_left _ hx) hxa).le) hlx
  have hj : jumpPrefix v.2.2 x = jumpPrefix v.2.2 a := by
    unfold jumpPrefix Finsupp.sum
    apply Finset.sum_congr rfl
    intro c hc
    have he : c < x ↔ c < a :=
      ⟨fun h => h.trans hxa, fun h => (hl c (Finset.mem_union_right _ hc) h).trans hlx⟩
    by_cases h : c < x
    · simp only [h, he.mp h, ite_true]
    · have hn : ¬ c < a := fun hca => h (he.mpr hca)
      simp only [h, hn, ite_false]
  rw [← coefficients_eval k f x]
  change v.1 + v.2.1 x + jumpPrefix v.2.2 x = v.1 + jumpPrefix v.2.2 a
  rw [hp, hj, add_zero]

theorem rightValue_germ (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    ∃ u, a < u ∧ ∀ x, a < x → x < u → f x = rightValue k f a := by
  let v := (coefficientEquiv k).symm f
  let S := v.2.1.support ∪ v.2.2.support
  obtain ⟨u, hau, hu⟩ := exists_right_gap S a
  refine ⟨u, hau, ?_⟩
  intro x hax hxu
  have hp : v.2.1 x = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact (not_lt_of_ge (hu x (Finset.mem_union_left _ hx) hax).le) hxu
  have hj : jumpPrefix v.2.2 x = jumpPrefix v.2.2 a + v.2.2 a :=
    jumpPrefix_right v.2.2 a x hax
      (fun c hc hac => hxu.trans (hu c (Finset.mem_union_right _ hc) hac))
  rw [← coefficients_eval k f x]
  change v.1 + v.2.1 x + jumpPrefix v.2.2 x = v.1 + jumpPrefix v.2.2 a + v.2.2 a
  rw [hp, hj, add_zero, add_assoc]

theorem tailValue_germ (k : EulerKind) (f : EulerFunction k Γ) :
    ∃ l, ∀ x, x < l → f x = tailValue k f := by
  let v := (coefficientEquiv k).symm f
  let S := insert 0 (v.2.1.support ∪ v.2.2.support)
  have hS : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_⟩
  intro x hxl
  rw [← coefficients_eval k f x]
  apply stepEval_below
  intro a ha
  exact hxl.trans_le (Finset.min'_le S a (Finset.mem_insert_of_mem ha))

theorem leftValue_eq_iff (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) (m : ℤ) :
    leftValue k f a = m ↔ ∃ l, l < a ∧ ∀ x, l < x → x < a → f x = m := by
  constructor
  · intro h
    simpa only [h] using leftValue_germ k f a
  · rintro ⟨l, hla, hm⟩
    obtain ⟨l', hl'a, hg⟩ := leftValue_germ k f a
    obtain ⟨x, hx, hxa⟩ := exists_between (max_lt_iff.mpr ⟨hla, hl'a⟩)
    exact (hg x ((le_max_right l l').trans_lt hx) hxa).symm.trans
      (hm x ((le_max_left l l').trans_lt hx) hxa)

theorem rightValue_eq_iff (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) (m : ℤ) :
    rightValue k f a = m ↔ ∃ u, a < u ∧ ∀ x, a < x → x < u → f x = m := by
  constructor
  · intro h
    simpa only [h] using rightValue_germ k f a
  · rintro ⟨u, hau, hm⟩
    obtain ⟨u', hau', hg⟩ := rightValue_germ k f a
    obtain ⟨x, hax, hx⟩ := exists_between (lt_min_iff.mpr ⟨hau, hau'⟩)
    exact (hg x hax (hx.trans_le (min_le_right u u'))).symm.trans
      (hm x hax (hx.trans_le (min_le_left u u')))

theorem tailValue_eq_iff (k : EulerKind) (f : EulerFunction k Γ) (m : ℤ) :
    tailValue k f = m ↔ ∃ l, ∀ x, x < l → f x = m := by
  constructor
  · intro h
    simpa only [h] using tailValue_germ k f
  · rintro ⟨l, hm⟩
    obtain ⟨l', hg⟩ := tailValue_germ k f
    obtain ⟨x, hx⟩ := exists_lt (min l l')
    exact (hg x (hx.trans_le (min_le_right l l'))).symm.trans
      (hm x (hx.trans_le (min_le_left l l')))

theorem leftValue_mem_range (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    leftValue k f a ∈ Set.range (f : Γ → ℤ) := by
  obtain ⟨l, hla, h⟩ := leftValue_germ k f a
  obtain ⟨x, hlx, hxa⟩ := exists_between hla
  exact ⟨x, h x hlx hxa⟩

theorem rightValue_mem_range (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    rightValue k f a ∈ Set.range (f : Γ → ℤ) := by
  obtain ⟨u, hau, h⟩ := rightValue_germ k f a
  obtain ⟨x, hax, hxu⟩ := exists_between hau
  exact ⟨x, h x hax hxu⟩

theorem tailValue_mem_range (k : EulerKind) (f : EulerFunction k Γ) :
    tailValue k f ∈ Set.range (f : Γ → ℤ) := by
  obtain ⟨l, h⟩ := tailValue_germ k f
  obtain ⟨x, hx⟩ := exists_lt l
  exact ⟨x, h x hx⟩

theorem pointCoefficient_eq (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    ((coefficientEquiv k).symm f).2.1 a = f a - leftValue k f a := by
  rw [← coefficients_eval k f a]
  unfold stepEval leftValue
  ring

theorem rayCoefficient_eq (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    ((coefficientEquiv k).symm f).2.2 a = rightValue k f a - leftValue k f a := by
  simp only [rightValue, add_sub_cancel_left]

end DiamondIntegral.Section4.EulerFunction
