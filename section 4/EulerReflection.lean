module

public import «section 4».EulerPointwise
public import «section 4».EulerIntervals

/-! Reflection of actual finite-jump functions, and invariance of the unary
Euler functional under that reflection. This constructs convolution fibres. -/

@[expose] public noncomputable section
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

omit [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [IsOrderedAddMonoid Γ] in
theorem reflection_point_iff (t a x : Γ) : x = t - a ↔ t - x = a := by
  constructor
  · intro h
    apply sub_eq_iff_eq_add.mpr
    exact (eq_sub_iff_add_eq.mp h).symm.trans (add_comm x a)
  · intro h
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm x a).trans (sub_eq_iff_eq_add.mp h).symm

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] in
theorem reflection_ray_iff (t a x : Γ) : x < t - a ↔ a < t - x := by
  rw [lt_sub_iff_add_lt, lt_sub_iff_add_lt]
  rw [add_comm x a]

def reflectAt (k : EulerKind) (t : Γ) (f : EulerFunction k Γ) : EulerFunction k Γ :=
  let v := (coefficientEquiv k).symm f
  v.1 • line k + v.2.1.sum (fun a n => n • point k (t - a)) +
    v.2.2.sum (fun a n => n • leftRay k (t - a))

theorem reflectAt_eval (k : EulerKind) (t : Γ) (f : EulerFunction k Γ) (x : Γ) :
    reflectAt k t f x = f (t - x) := by
  have hp (a : Γ) (n : ℤ) : (if x = t - a then n else 0) =
      (if t - x = a then n else 0) := by
    by_cases h : x = t - a
    · simp [h]
    · have he : ¬ t - x = a := fun hh => h ((reflection_point_iff t a x).mpr hh)
      simp [h, he]
  have hq (a : Γ) (n : ℤ) : (if x < t - a then n else 0) =
      (if a < t - x then n else 0) := by
    by_cases h : x < t - a
    · have he := (reflection_ray_iff t a x).mp h
      simp [h, he]
    · have he : ¬ a < t - x := fun hh => h ((reflection_ray_iff t a x).mpr hh)
      simp [h, he]
  simp only [reflectAt, eval_add, eval_finsuppSum, eval_zsmul,
    line_eval, point_eval, leftRay_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one, mul_ite, mul_zero]
  simp_rw [hp, hq]
  rw [Finsupp.sum_ite_self_eq]
  exact coefficients_eval k f (t - x)

theorem reflectAt_add (k : EulerKind) (t : Γ) (f g : EulerFunction k Γ) :
    reflectAt k t (f + g) = reflectAt k t f + reflectAt k t g := by
  apply eval_injective k
  funext x
  change reflectAt k t (f + g) x = (reflectAt k t f + reflectAt k t g) x
  simp only [reflectAt_eval, eval_add]

theorem reflectAt_zero (k : EulerKind) (t : Γ) :
    reflectAt k t (0 : EulerFunction k Γ) = 0 := by
  apply eval_injective k
  funext x
  change reflectAt k t (0 : EulerFunction k Γ) x = (0 : EulerFunction k Γ) x
  simp only [reflectAt_eval, eval_zero]

def reflection (k : EulerKind) (t : Γ) : EulerFunction k Γ →+ EulerFunction k Γ where
  toFun := reflectAt k t
  map_zero' := reflectAt_zero k t
  map_add' := reflectAt_add k t

theorem reflectAt_point (k : EulerKind) (t a : Γ) :
    reflectAt k t (point k a) = point k (t - a) := by
  apply eval_injective k
  funext x
  change reflectAt k t (point k a) x = point k (t - a) x
  simp only [reflectAt_eval, point_eval, reflection_point_iff]

theorem reflectAt_ray (k : EulerKind) (t a : Γ) :
    reflectAt k t (ray k a) = leftRay k (t - a) := by
  apply eval_injective k
  funext x
  change reflectAt k t (ray k a) x = leftRay k (t - a) x
  simp only [reflectAt_eval, ray_eval, leftRay_eval, reflection_ray_iff]

theorem reflectAt_line (k : EulerKind) (t : Γ) : reflectAt k t (line k) = line k := by
  apply eval_injective k
  funext x
  change reflectAt k t (line k) x = line k x
  simp only [reflectAt_eval, line_eval]

theorem reflection_involutive (k : EulerKind) (t : Γ) :
    Function.Involutive (reflectAt k t : EulerFunction k Γ → EulerFunction k Γ) := by
  intro f
  apply eval_injective k
  funext x
  change reflectAt k t (reflectAt k t f) x = f x
  rw [reflectAt_eval, reflectAt_eval, sub_sub_cancel]

theorem totalEuler_reflection (k : EulerKind) (t : Γ) :
    (totalEuler k).toAddMonoidHom.comp (reflection k t) = (totalEuler k).toAddMonoidHom := by
  apply additive_ext k
  · change totalEuler k (reflectAt k t (line k)) = totalEuler k (line k)
    rw [reflectAt_line]
  · intro a
    change totalEuler k (reflectAt k t (point k a)) = totalEuler k (point k a)
    rw [reflectAt_point, totalEuler_point, totalEuler_point]
  · intro a
    change totalEuler k (reflectAt k t (ray k a)) = totalEuler k (ray k a)
    rw [reflectAt_ray, totalEuler_leftRay, totalEuler_ray]

theorem totalEuler_reflectAt (k : EulerKind) (t : Γ) (f : EulerFunction k Γ) :
    totalEuler k (reflectAt k t f) = totalEuler k f :=
  DFunLike.congr_fun (totalEuler_reflection k t) f

end DiamondIntegral.Section4.EulerFunction
