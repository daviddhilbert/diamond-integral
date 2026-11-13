module

public import «section 4».EulerBoundedComparison

/-! Transport actual unary Euler functions along order isomorphisms.
This preserves both Euler functionals and bounded support; it does not
claim convolution multiplicativity for a nonadditive order isomorphism. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ Δ Ε : Type*}
  [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]
  [LinearOrder Δ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]
  [LinearOrder Ε] [DenselyOrdered Ε] [NoMinOrder Ε] [NoMaxOrder Ε] [AddCommGroup Ε]

def orderPush (k : EulerKind) (e : Γ ≃o Δ) (f : EulerFunction k Γ) : EulerFunction k Δ :=
  let v := (coefficientEquiv k).symm f
  v.1 • line k + v.2.1.sum (fun a n => n • point k (e a)) +
    v.2.2.sum (fun a n => n • ray k (e a))

theorem orderPush_eval (k : EulerKind) (e : Γ ≃o Δ) (f : EulerFunction k Γ) (x : Δ) :
    orderPush k e f x = f (e.symm x) := by
  have hp (a : Γ) (n : ℤ) : (if x = e a then n else 0) =
      (if e.symm x = a then n else 0) := by
    by_cases h : x = e a
    · subst x
      simp
    · have hi : e.symm x ≠ a := by
        intro he
        apply h
        rw [← he, e.apply_symm_apply]
      simp [h, hi]
  have hq (a : Γ) (n : ℤ) : (if e a < x then n else 0) =
      (if a < e.symm x then n else 0) := by
    by_cases h : e a < x
    · simp [h, e.lt_symm_apply.mpr h]
    · have hi : ¬ a < e.symm x := fun hh => h (e.lt_symm_apply.mp hh)
      simp [h, hi]
  simp only [orderPush, eval_add, eval_finsuppSum, eval_zsmul, line_eval, point_eval, ray_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one, mul_ite, mul_zero]
  simp_rw [hp, hq]
  rw [Finsupp.sum_ite_self_eq]
  exact coefficients_eval k f (e.symm x)

def orderTransport (k : EulerKind) (e : Γ ≃o Δ) : EulerFunction k Γ ≃+ EulerFunction k Δ where
  toFun := orderPush k e
  invFun := orderPush k e.symm
  left_inv f := by
    apply eval_injective k
    funext x
    change orderPush k e.symm (orderPush k e f) x = f x
    simp only [orderPush_eval, OrderIso.symm_symm, e.symm_apply_apply]
  right_inv f := by
    apply eval_injective k
    funext x
    change orderPush k e (orderPush k e.symm f) x = f x
    simp only [orderPush_eval, OrderIso.symm_symm, e.apply_symm_apply]
  map_add' f g := by
    apply eval_injective k
    funext x
    change orderPush k e (f + g) x = (orderPush k e f + orderPush k e g) x
    simp only [orderPush_eval, eval_add]

theorem orderPush_trans (k : EulerKind) (e : Γ ≃o Δ) (d : Δ ≃o Ε) (f : EulerFunction k Γ) :
    orderPush k d (orderPush k e f) = orderPush k (e.trans d) f := by
  apply eval_injective k
  funext x
  change orderPush k d (orderPush k e f) x = orderPush k (e.trans d) f x
  rw [orderPush_eval, orderPush_eval, orderPush_eval]
  rfl

theorem orderPush_line (k : EulerKind) (e : Γ ≃o Δ) : orderPush k e (line k) = line k := by
  apply eval_injective k
  funext x
  change orderPush k e (line k) x = line k x
  rw [orderPush_eval, line_eval, line_eval]

theorem orderPush_point (k : EulerKind) (e : Γ ≃o Δ) (a : Γ) :
    orderPush k e (point k a) = point k (e a) := by
  apply eval_injective k
  funext x
  change orderPush k e (point k a) x = point k (e a) x
  have he : e.symm x = a ↔ x = e a := by
    constructor
    · intro h
      rw [← h, e.apply_symm_apply]
    · intro h
      rw [h, e.symm_apply_apply]
  simp only [orderPush_eval, point_eval, he]

theorem orderPush_ray (k : EulerKind) (e : Γ ≃o Δ) (a : Γ) :
    orderPush k e (ray k a) = ray k (e a) := by
  apply eval_injective k
  funext x
  change orderPush k e (ray k a) x = ray k (e a) x
  simp only [orderPush_eval, ray_eval, e.lt_symm_apply]

theorem totalEuler_orderPush (k : EulerKind) (e : Γ ≃o Δ) (f : EulerFunction k Γ) :
    totalEuler k (orderPush k e f) = totalEuler k f := by
  have he : (totalEuler (Γ := Δ) k).toAddMonoidHom.comp
      (orderTransport k e).toAddMonoidHom = (totalEuler (Γ := Γ) k).toAddMonoidHom := by
    apply additive_ext k
    · change totalEuler k (orderPush k e (line k)) = totalEuler k (line k)
      rw [orderPush_line, totalEuler_line, totalEuler_line]
    · intro a
      change totalEuler k (orderPush k e (point k a)) = totalEuler k (point k a)
      rw [orderPush_point, totalEuler_point, totalEuler_point]
    · intro a
      change totalEuler k (orderPush k e (ray k a)) = totalEuler k (ray k a)
      rw [orderPush_ray, totalEuler_ray, totalEuler_ray]
  exact DFunLike.congr_fun he f

theorem IsDoublyBounded.orderPush {k : EulerKind} {f : EulerFunction k Γ}
    (hf : IsDoublyBounded f) (e : Γ ≃o Δ) : IsDoublyBounded (orderPush k e f) := by
  obtain ⟨a, b, h⟩ := hf
  refine ⟨e a, e b, ?_⟩
  intro x hx
  have hfx : f (e.symm x) ≠ 0 := by simpa only [orderPush_eval] using hx
  obtain ⟨hl, hu⟩ := h (e.symm x) hfx
  constructor
  · simpa only [e.apply_symm_apply] using e.monotone hl
  · simpa only [e.apply_symm_apply] using e.monotone hu

end DiamondIntegral.Section4.EulerFunction
