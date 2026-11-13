module

public import «section 4».EulerConvolution

/-! The complete sign and endpoint cases of the bounded-interval product
table. Multiplication has already been identified with actual unary Euler
convolution, so these are identities of the constructed integral. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

omit [IsOrderedAddMonoid Γ] in
theorem boundedInterval_nonneg_form (k : EulerKind) (a : Γ) (ha : 0 ≤ a) :
    boundedInterval k a = ray k 0 - ray k a - point k a := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    rw [boundedInterval_zero]
    abel
  · rw [boundedInterval_positive k a ha, openInterval, ite_eq_left ha]

omit [IsOrderedAddMonoid Γ] in
theorem boundedInterval_nonpos_form (k : EulerKind) (a : Γ) (ha : a ≤ 0) :
    boundedInterval k a = ray k a - ray k 0 - point k 0 := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    rw [boundedInterval_zero]
    abel
  · rw [boundedInterval_negative k a ha, openInterval, ite_eq_left ha]

theorem point_mul_openInterval (k : EulerKind) (a b c : Γ) :
    point k a * openInterval k b c = openInterval k (a + b) (a + c) := by
  by_cases h : b < c
  · simp only [openInterval, h, add_lt_add_iff_left, ite_true, mul_sub,
      point_ray, point_mul]
  · simp only [openInterval, h, add_lt_add_iff_left, ite_false, mul_zero]

omit [IsOrderedAddMonoid Γ] in
theorem point_mul_boundedInterval_zero (k : EulerKind) (a : Γ) :
    point k a * boundedInterval k 0 = -point k a := by
  rw [boundedInterval_zero, mul_neg, point_mul, add_zero]

theorem point_mul_boundedInterval (k : EulerKind) (a b : Γ) (hb : b ≠ 0) :
    point k a * boundedInterval k b =
      openInterval k (min a (a + b)) (max a (a + b)) := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hab : a + b < a := by simpa only [add_comm, zero_add, add_zero] using add_lt_add_left hb a
    rw [boundedInterval_negative k b hb, point_mul_openInterval, add_zero,
      min_eq_right hab.le, max_eq_left hab.le]
  · have hab : a < a + b := by simpa only [add_comm, zero_add, add_zero] using add_lt_add_left hb a
    rw [boundedInterval_positive k b hb, point_mul_openInterval, add_zero,
      min_eq_left hab.le, max_eq_right hab.le]

omit [IsOrderedAddMonoid Γ] in
theorem openInterval_nonneg_decomposition (k : EulerKind) (a b : Γ)
    (ha : 0 ≤ a) (hab : a < b) :
    openInterval k a b = boundedInterval k b - boundedInterval k a - point k a := by
  rw [boundedInterval_nonneg_form k a ha, boundedInterval_nonneg_form k b (ha.trans hab.le),
    openInterval, ite_eq_left hab]
  abel

omit [IsOrderedAddMonoid Γ] in
theorem openInterval_nonpos_decomposition (k : EulerKind) (a b : Γ)
    (hb : b ≤ 0) (hab : a < b) :
    openInterval k a b = boundedInterval k a - boundedInterval k b - point k b := by
  rw [boundedInterval_nonpos_form k a (hab.le.trans hb), boundedInterval_nonpos_form k b hb,
    openInterval, ite_eq_left hab]
  abel

omit [IsOrderedAddMonoid Γ] in
theorem openInterval_cross_decomposition (k : EulerKind) (a b : Γ)
    (ha : a < 0) (hb : 0 < b) :
    openInterval k a b = boundedInterval k a + boundedInterval k b + point k 0 := by
  rw [boundedInterval_nonpos_form k a ha.le, boundedInterval_nonneg_form k b hb.le,
    openInterval, ite_eq_left (ha.trans hb)]
  abel

omit [IsOrderedAddMonoid Γ] in
theorem ray_point (k : EulerKind) (a b : Γ) :
    ray k a * point k b = ray k (a + b) := by rw [mul_comm, point_ray, add_comm]

theorem boundedInterval_mul_nonneg (k : EulerKind) (a b : Γ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    boundedInterval k a * boundedInterval k b = -boundedInterval k (a + b) := by
  rw [boundedInterval_nonneg_form k a ha, boundedInterval_nonneg_form k b hb,
    boundedInterval_nonneg_form k (a + b) (add_nonneg ha hb)]
  simp only [sub_mul, mul_sub, ray_mul, ray_point, point_ray, point_mul, zero_add, add_zero]
  abel

theorem boundedInterval_mul_nonpos (k : EulerKind) (a b : Γ) (ha : a ≤ 0) (hb : b ≤ 0) :
    boundedInterval k a * boundedInterval k b = -boundedInterval k (a + b) := by
  rw [boundedInterval_nonpos_form k a ha, boundedInterval_nonpos_form k b hb,
    boundedInterval_nonpos_form k (a + b) (add_nonpos ha hb)]
  simp only [sub_mul, mul_sub, ray_mul, ray_point, point_ray, point_mul, zero_add, add_zero]
  abel

omit [IsOrderedAddMonoid Γ] in
theorem boundedInterval_mul_opposite (k : EulerKind) (a b : Γ) (ha : a < 0) (hb : 0 < b) :
    boundedInterval k a * boundedInterval k b =
      -boundedInterval k a - boundedInterval k b - point k 0 := by
  rw [boundedInterval_nonpos_form k a ha.le, boundedInterval_nonneg_form k b hb.le]
  simp only [sub_mul, mul_sub, ray_mul, ray_point, point_ray, point_mul, zero_add, add_zero]
  abel

omit [IsOrderedAddMonoid Γ] in
theorem boundedInterval_mul_opposite' (k : EulerKind) (a b : Γ) (ha : 0 < a) (hb : b < 0) :
    boundedInterval k a * boundedInterval k b =
      -boundedInterval k a - boundedInterval k b - point k 0 := by
  rw [mul_comm, boundedInterval_mul_opposite k b a hb ha]
  abel

end DiamondIntegral.Section4.EulerFunction
