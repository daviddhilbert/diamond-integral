module

public import «section 4».EulerDecomposition

/-! Pointwise products remain actual finite-jump functions. This is a
different operation from the generator-ring multiplication. It constructs
the integrands used by Euler convolution without assuming closure. -/

@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

theorem coefficients_eval (k : EulerKind) (f : EulerFunction k Γ) (x : Γ) :
    stepEval ((coefficientEquiv k).symm f) x = f x := by
  simpa only [ofCoefficients, AddEquiv.apply_symm_apply] using
    (ofCoefficients_eval k ((coefficientEquiv k).symm f) x).symm

def restrictRay (k : EulerKind) (a : Γ) (f : EulerFunction k Γ) : EulerFunction k Γ :=
  let v := (coefficientEquiv k).symm f
  v.1 • ray k a +
    v.2.1.sum (fun b n => (if a < b then n else 0) • point k b) +
    v.2.2.sum (fun b n => n • ray k (max a b))

theorem restrictRay_eval (k : EulerKind) (a : Γ) (f : EulerFunction k Γ) (x : Γ) :
    restrictRay k a f x = if a < x then f x else 0 := by
  have hp (b : Γ) (n : ℤ) :
      (if a < b then n else 0) * (if x = b then 1 else 0) =
      if a < x then (if x = b then n else 0) else 0 := by
    by_cases hxb : x = b
    · subst b; simp
    · simp [hxb]
  simp only [restrictRay, eval_add, eval_finsuppSum, eval_zsmul, point_eval, ray_eval]
  simp only [zsmul_eq_mul, Int.cast_id]
  simp_rw [hp]
  by_cases hax : a < x
  · simp only [hax, ite_true, max_lt_iff, true_and]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finsupp.sum_ite_self_eq]
    exact coefficients_eval k f x
  · simp [hax, max_lt_iff]

def pointwiseProduct (k : EulerKind) (f g : EulerFunction k Γ) : EulerFunction k Γ :=
  let v := (coefficientEquiv k).symm f
  v.1 • g + v.2.1.sum (fun a n => n • (g a • point k a)) +
    v.2.2.sum (fun a n => n • restrictRay k a g)

theorem pointwiseProduct_eval (k : EulerKind) (f g : EulerFunction k Γ) (x : Γ) :
    pointwiseProduct k f g x = f x * g x := by
  have hp (a : Γ) (n : ℤ) :
      n * (g a * (if x = a then 1 else 0)) = (if x = a then n else 0) * g x := by
    by_cases hxa : x = a
    · subst a; simp
    · simp [hxa]
  have hq (a : Γ) (n : ℤ) :
      n * (if a < x then g x else 0) = (if a < x then n else 0) * g x := by
    split_ifs <;> simp
  have hsum (p : Γ →₀ ℤ) (h : Γ → ℤ → ℤ) :
      p.sum (fun a n => h a n * g x) = p.sum h * g x :=
    (Finset.sum_mul _ _ _).symm
  simp only [pointwiseProduct, eval_add, eval_finsuppSum, eval_zsmul,
    point_eval, restrictRay_eval]
  simp only [zsmul_eq_mul, Int.cast_id]
  simp_rw [hp, hq]
  rw [hsum, hsum, Finsupp.sum_ite_self_eq]
  calc
    _ = stepEval ((coefficientEquiv k).symm f) x * g x := by
      unfold stepEval jumpPrefix
      ring
    _ = f x * g x := by rw [coefficients_eval]

theorem pointwiseProduct_comm (k : EulerKind) (f g : EulerFunction k Γ) :
    pointwiseProduct k f g = pointwiseProduct k g f := by
  apply eval_injective k
  funext x
  exact (pointwiseProduct_eval k f g x).trans
    ((mul_comm (f x) (g x)).trans (pointwiseProduct_eval k g f x).symm)

theorem pointwiseProduct_add_left (k : EulerKind) (f g h : EulerFunction k Γ) :
    pointwiseProduct k (f + g) h = pointwiseProduct k f h + pointwiseProduct k g h := by
  apply eval_injective k
  funext x
  change pointwiseProduct k (f + g) h x = (pointwiseProduct k f h + pointwiseProduct k g h) x
  simp only [pointwiseProduct_eval, eval_add]
  exact add_mul _ _ _

theorem pointwiseProduct_add_right (k : EulerKind) (f g h : EulerFunction k Γ) :
    pointwiseProduct k f (g + h) = pointwiseProduct k f g + pointwiseProduct k f h := by
  rw [pointwiseProduct_comm k f (g + h), pointwiseProduct_add_left,
    pointwiseProduct_comm k g f, pointwiseProduct_comm k h f]

theorem pointwiseProduct_zero_left (k : EulerKind) (f : EulerFunction k Γ) :
    pointwiseProduct k 0 f = 0 := by
  apply eval_injective k
  funext x
  change pointwiseProduct k 0 f x = (0 : EulerFunction k Γ) x
  simp only [pointwiseProduct_eval, eval_zero, zero_mul]

theorem pointwiseProduct_point (k : EulerKind) (a : Γ) (f : EulerFunction k Γ) :
    pointwiseProduct k (point k a) f = f a • point k a := by
  apply eval_injective k
  funext x
  change pointwiseProduct k (point k a) f x = (f a • point k a) x
  simp only [pointwiseProduct_eval, point_eval, eval_zsmul]
  simp only [zsmul_eq_mul, Int.cast_id]
  by_cases hxa : x = a
  · subst x; simp
  · simp [hxa]

theorem pointwiseProduct_line (k : EulerKind) (f : EulerFunction k Γ) :
    pointwiseProduct k (line k) f = f := by
  apply eval_injective k
  funext x
  change pointwiseProduct k (line k) f x = f x
  rw [pointwiseProduct_eval, line_eval, one_mul]

theorem pointwiseProduct_ray (k : EulerKind) (a : Γ) (f : EulerFunction k Γ) :
    pointwiseProduct k (ray k a) f = restrictRay k a f := by
  apply eval_injective k
  funext x
  change pointwiseProduct k (ray k a) f x = restrictRay k a f x
  rw [pointwiseProduct_eval, ray_eval, restrictRay_eval]
  split_ifs <;> simp

end DiamondIntegral.Section4.EulerFunction
