module

public import «section 4».EulerReflection

/-! Euler integration of actual convolution fibres agrees with the checked
generator-ring product. The integral here is the constructed unary Euler
functional on finite-jump functions. First-order Gamma descent and the
paper's multivariable Euler theory remain separate obligations. -/

@[expose] public noncomputable section
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

omit [IsOrderedAddMonoid Γ] in
theorem pointwiseProduct_ray_leftRay (k : EulerKind) (a b : Γ) :
    pointwiseProduct k (ray k a) (leftRay k b) = openInterval k a b := by
  apply eval_injective k
  funext x
  change pointwiseProduct k (ray k a) (leftRay k b) x = openInterval k a b x
  rw [pointwiseProduct_eval, ray_eval, leftRay_eval, openInterval_eval]
  by_cases ha : a < x <;> by_cases hb : x < b <;> simp [ha, hb]

def convolutionValue (k : EulerKind) (f g : EulerFunction k Γ) (t : Γ) : ℤ :=
  totalEuler k (pointwiseProduct k f (reflectAt k t g))

theorem convolutionValue_line (k : EulerKind) (g : EulerFunction k Γ) (t : Γ) :
    convolutionValue k (line (Γ := Γ) k) g t = totalEuler k g := by
  rw [convolutionValue, pointwiseProduct_line, totalEuler_reflectAt]

theorem convolutionValue_point (k : EulerKind) (a : Γ) (g : EulerFunction k Γ) (t : Γ) :
    convolutionValue k (point k a) g t = g (t - a) := by
  rw [convolutionValue, pointwiseProduct_point, map_zsmul, totalEuler_point]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one, reflectAt_eval]

theorem convolutionValue_ray_line (k : EulerKind) (a t : Γ) :
    convolutionValue k (ray k a) (line (Γ := Γ) k) t = k.rayValue := by
  rw [convolutionValue, reflectAt_line, pointwiseProduct_comm, pointwiseProduct_line,
    totalEuler_ray]

theorem convolutionValue_ray_point (k : EulerKind) (a b t : Γ) :
    convolutionValue k (ray k a) (point k b) t = if a < t - b then 1 else 0 := by
  rw [convolutionValue, reflectAt_point, pointwiseProduct_comm, pointwiseProduct_point,
    map_zsmul, totalEuler_point]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one, ray_eval]

theorem convolutionValue_ray_ray (k : EulerKind) (a b t : Γ) :
    convolutionValue k (ray k a) (ray k b) t = if a < t - b then -1 else 0 := by
  rw [convolutionValue, reflectAt_ray, pointwiseProduct_ray_leftRay, totalEuler_openInterval]

def convolutionRight (k : EulerKind) (t : Γ) (f : EulerFunction k Γ) :
    EulerFunction k Γ →+ ℤ where
  toFun g := convolutionValue k f g t
  map_zero' := by
    simp only [convolutionValue, reflectAt_zero]
    rw [pointwiseProduct_comm, pointwiseProduct_zero_left, map_zero]
  map_add' g h := by
    simp only [convolutionValue, reflectAt_add, pointwiseProduct_add_right, map_add]

def convolutionBilinear (k : EulerKind) (t : Γ) :
    EulerFunction k Γ →+ (EulerFunction k Γ →+ ℤ) where
  toFun := convolutionRight k t
  map_zero' := by
    apply AddMonoidHom.ext
    intro g
    change convolutionValue k 0 g t = 0
    rw [convolutionValue, pointwiseProduct_zero_left, map_zero]
  map_add' f h := by
    apply AddMonoidHom.ext
    intro g
    change convolutionValue k (f + h) g t = convolutionValue k f g t + convolutionValue k h g t
    simp only [convolutionValue, pointwiseProduct_add_left, map_add]

def productBilinear (k : EulerKind) (t : Γ) :
    EulerFunction k Γ →+ (EulerFunction k Γ →+ ℤ) where
  toFun f := {
    toFun g := (f * g) t
    map_zero' := by rw [mul_zero, eval_zero]
    map_add' g h := by rw [mul_add, eval_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro g
    change ((0 : EulerFunction k Γ) * g) t = 0
    rw [zero_mul, eval_zero]
  map_add' f h := by
    apply AddMonoidHom.ext
    intro g
    change ((f + h) * g) t = (f * g) t + (h * g) t
    rw [add_mul, eval_add]

/-- Generator induction is justified by the proved canonical decomposition
of actual functions. In particular, associativity is not an extra premise. -/
theorem convolutionBilinear_eq_product (k : EulerKind) (t : Γ) :
    convolutionBilinear k t = productBilinear k t := by
  apply additive_ext k
  · apply additive_ext k
    · change convolutionValue k (line (Γ := Γ) k) (line (Γ := Γ) k) t = (line (Γ := Γ) k * line (Γ := Γ) k) t
      rw [convolutionValue_line, totalEuler_line, line_mul, eval_zsmul, line_eval]
      simp
    · intro b
      change convolutionValue k (line (Γ := Γ) k) (point k b) t = (line (Γ := Γ) k * point k b) t
      rw [convolutionValue_line, totalEuler_point, line_point, line_eval]
    · intro b
      change convolutionValue k (line (Γ := Γ) k) (ray k b) t = (line (Γ := Γ) k * ray k b) t
      rw [convolutionValue_line, totalEuler_ray, line_ray, eval_zsmul, line_eval]
      simp
  · intro a
    apply additive_ext k
    · change convolutionValue k (point k a) (line (Γ := Γ) k) t = (point k a * line (Γ := Γ) k) t
      rw [convolutionValue_point, line_eval, mul_comm (point k a) (line (Γ := Γ) k), line_point, line_eval]
    · intro b
      change convolutionValue k (point k a) (point k b) t = (point k a * point k b) t
      rw [convolutionValue_point, point_eval, point_mul, point_eval]
      simp only [sub_eq_iff_eq_add, add_comm]
    · intro b
      change convolutionValue k (point k a) (ray k b) t = (point k a * ray k b) t
      rw [convolutionValue_point, ray_eval, point_ray, ray_eval]
      simp only [lt_sub_iff_add_lt, add_comm]
  · intro a
    apply additive_ext k
    · change convolutionValue k (ray k a) (line (Γ := Γ) k) t = (ray k a * line (Γ := Γ) k) t
      rw [convolutionValue_ray_line, mul_comm (ray k a) (line (Γ := Γ) k), line_ray,
        eval_zsmul, line_eval]
      simp
    · intro b
      change convolutionValue k (ray k a) (point k b) t = (ray k a * point k b) t
      rw [convolutionValue_ray_point, mul_comm (ray k a) (point k b), point_ray, ray_eval]
      simp only [lt_sub_iff_add_lt, add_comm]
    · intro b
      change convolutionValue k (ray k a) (ray k b) t = (ray k a * ray k b) t
      rw [convolutionValue_ray_ray, ray_mul, eval_neg, ray_eval]
      simp only [lt_sub_iff_add_lt]
      split_ifs <;> norm_num

theorem convolutionValue_eq_product (k : EulerKind) (f g : EulerFunction k Γ) (t : Γ) :
    convolutionValue k f g t = (f * g) t :=
  DFunLike.congr_fun (DFunLike.congr_fun (convolutionBilinear_eq_product k t) f) g

theorem convolution_associative (k : EulerKind) (f g h : EulerFunction k Γ) (t : Γ) :
    convolutionValue k (f * g) h t = convolutionValue k f (g * h) t := by
  rw [convolutionValue_eq_product, convolutionValue_eq_product, mul_assoc]

theorem convolution_commutative (k : EulerKind) (f g : EulerFunction k Γ) (t : Γ) :
    convolutionValue k f g t = convolutionValue k g f t := by
  rw [convolutionValue_eq_product, convolutionValue_eq_product, mul_comm]

end DiamondIntegral.Section4.EulerFunction
