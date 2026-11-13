module

public import «section 4».EulerBoundedComparison

/-! Actual point and bounded-interval generators of the bounded function
ring, and a proved additive generator principle for its quotient. -/

set_option autoImplicit false

@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

omit [IsOrderedAddMonoid Γ] in
theorem isDoublyBounded_openInterval (k : EulerKind) (a b : Γ) :
    IsDoublyBounded (openInterval k a b) := by
  refine ⟨a, b, ?_⟩
  intro x hx
  have h : a < x ∧ x < b := by
    by_contra hn
    exact hx (by rw [openInterval_eval, ite_eq_right hn])
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

omit [IsOrderedAddMonoid Γ] in
theorem isDoublyBounded_boundedInterval (k : EulerKind) (a : Γ) :
    IsDoublyBounded (boundedInterval k a) := by
  rcases lt_trichotomy 0 a with ha | ha | ha
  · rw [boundedInterval_positive k a ha]
    exact isDoublyBounded_openInterval k 0 a
  · subst a
    rw [boundedInterval_zero]
    exact (isDoublyBounded_point k 0).neg
  · rw [boundedInterval_negative k a ha]
    exact isDoublyBounded_openInterval k a 0

def boundedPoint (k : EulerKind) (a : Γ) : boundedSubring (Γ := Γ) k :=
  ⟨point k a, isDoublyBounded_point k a⟩

def boundedIntervalElement (k : EulerKind) (a : Γ) : boundedSubring (Γ := Γ) k :=
  ⟨boundedInterval k a, isDoublyBounded_boundedInterval k a⟩

theorem boundedPoint_coe (k : EulerKind) (a : Γ) :
    (boundedPoint k a : EulerFunction k Γ) = point k a := rfl

theorem boundedIntervalElement_coe (k : EulerKind) (a : Γ) :
    (boundedIntervalElement k a : EulerFunction k Γ) = boundedInterval k a := rfl

theorem boundedPoint_zero (k : EulerKind) : boundedPoint k (0 : Γ) = 1 :=
  Subtype.ext (point_zero k)

theorem boundedEuler_point (k : EulerKind) (a : Γ) : boundedEuler k (boundedPoint k a) = 1 :=
  totalEuler_point k a

theorem boundedEuler_interval (k : EulerKind) (a : Γ) :
    boundedEuler k (boundedIntervalElement k a) = -1 := totalEuler_boundedInterval k a

def boundedRayDifference (k : EulerKind) (a : Γ) : boundedSubring (Γ := Γ) k :=
  if 0 < a then -boundedIntervalElement k a - boundedPoint k a
  else boundedIntervalElement k a + boundedPoint k 0

theorem boundedRayDifference_coe (k : EulerKind) (a : Γ) :
    (boundedRayDifference k a : EulerFunction k Γ) = ray k a - ray k 0 := by
  by_cases ha : 0 < a
  · rw [boundedRayDifference, ite_eq_left ha]
    change -boundedInterval k a - point k a = ray k a - ray k 0
    rw [boundedInterval_positive k a ha, openInterval, ite_eq_left ha]
    abel
  · rw [boundedRayDifference, ite_eq_right ha]
    change boundedInterval k a + point k 0 = ray k a - ray k 0
    by_cases ha0 : a < 0
    · rw [boundedInterval_negative k a ha0, openInterval, ite_eq_left ha0]
      abel
    · have he : a = 0 := le_antisymm (le_of_not_gt ha) (le_of_not_gt ha0)
      subst a
      rw [boundedInterval_zero]
      simp

def boundedCombination (k : EulerKind) (v : StepCoefficients Γ) : boundedSubring (Γ := Γ) k :=
  v.2.1.sum (fun a n => n • boundedPoint k a) +
    v.2.2.sum (fun a n => n • boundedRayDifference k a)

theorem boundedCombination_coe (k : EulerKind) (v : StepCoefficients Γ) :
    (boundedCombination k v : EulerFunction k Γ) =
      v.2.1.sum (fun a n => n • point k a) +
      v.2.2.sum (fun a n => n • (ray k a - ray k 0)) := by
  change (boundedSubring (Γ := Γ) k).subtype (boundedCombination k v) = _
  simp only [boundedCombination, Finsupp.sum, map_add, map_sum, map_zsmul]
  simp only [Subring.subtype_apply, boundedPoint_coe, boundedRayDifference_coe]

omit [IsOrderedAddMonoid Γ] in
theorem balanced_ray_sum_eval (k : EulerKind) (q : Γ →₀ ℤ)
    (hq : coefficientSum q = 0) (x : Γ) :
    (q.sum (fun a n => n • (ray k a - ray k 0)) : EulerFunction k Γ) x = jumpPrefix q x := by
  simp only [eval_finsuppSum, eval_zsmul, eval_sub, ray_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_sub]
  unfold Finsupp.sum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change q.sum (fun a n => n * (if a < x then 1 else 0)) -
    coefficientSum q * (if 0 < x then 1 else 0) = jumpPrefix q x
  rw [hq, zero_mul, sub_zero]
  simp only [mul_ite, mul_one, mul_zero]
  rfl

theorem boundedCombination_eval (k : EulerKind) (v : StepCoefficients Γ)
    (hq : coefficientSum v.2.2 = 0) (x : Γ) :
    (boundedCombination k v : EulerFunction k Γ) x = v.2.1 x + jumpPrefix v.2.2 x := by
  rw [boundedCombination_coe, eval_add, balanced_ray_sum_eval k v.2.2 hq x]
  rw [eval_finsuppSum]
  simp only [eval_zsmul, point_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
  rw [Finsupp.sum_ite_self_eq]

theorem bounded_generator_expansion (k : EulerKind) (f : boundedSubring (Γ := Γ) k) :
    ∃ v : StepCoefficients Γ, v.1 = 0 ∧ coefficientSum v.2.2 = 0 ∧
      f = boundedCombination k v := by
  let v := (coefficientEquiv k).symm f.val
  obtain ⟨hc, hq⟩ := (isDoublyBounded_iff_coefficients k f.val).mp f.property
  refine ⟨v, hc, hq, ?_⟩
  apply Subtype.ext
  apply eval_injective k
  funext x
  change f.val x = (boundedCombination k v : EulerFunction k Γ) x
  rw [boundedCombination_eval k v hq x]
  rw [← coefficients_eval k f.val x]
  simp only [stepEval, hc, zero_add]
  rfl

theorem bounded_additive_ext {A : Type*} [AddCommGroup A] (k : EulerKind)
    (f g : boundedSubring (Γ := Γ) k →+ A)
    (hp : ∀ a, f (boundedPoint k a) = g (boundedPoint k a))
    (ho : ∀ a, f (boundedIntervalElement k a) = g (boundedIntervalElement k a)) : f = g := by
  have hq : ∀ a, f (boundedRayDifference k a) = g (boundedRayDifference k a) := by
    intro a
    by_cases ha : 0 < a
    · simp only [boundedRayDifference, ha, ite_true, map_sub, map_neg, hp, ho]
    · simp only [boundedRayDifference, ha, ite_false, map_add, hp, ho]
  apply AddMonoidHom.ext
  intro h
  obtain ⟨v, _, _, rfl⟩ := bounded_generator_expansion k h
  simp only [boundedCombination, Finsupp.sum, map_add, map_sum, map_zsmul, hp, hq]

end DiamondIntegral.Section4.EulerFunction
