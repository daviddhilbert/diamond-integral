module

public import «section 4».EulerOrderTransport
public import «section 4».EulerFiniteCuts

/-! Construct unary Euler pushforwards for finite pieces of increasing,
decreasing or constant maps. The fibre is an actual finite-jump function;
its Euler value is the constructed pushforward, and integration preserves
the total. Classification of every definable map into these pieces remains
a separate obligation. No Fubini theorem is assumed. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ Δ : Type*}
  [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]
  [IsOrderedAddMonoid Γ]
  [LinearOrder Δ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]

inductive UnaryBranch (Γ Δ : Type*) [LinearOrder Γ] [LinearOrder Δ] where
  | increasing (e : Γ ≃o Δ)
  | decreasing (e : Γ ≃o Δ)
  | constant (c : Δ)

def UnaryBranch.apply (b : UnaryBranch Γ Δ) (x : Γ) : Δ :=
  match b with
  | .increasing e => e x
  | .decreasing e => e (-x)
  | .constant c => c

def UnaryBranch.push (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) : EulerFunction k Δ :=
  match b with
  | .increasing e => orderPush k e f
  | .decreasing e => orderPush k e (reflectAt k 0 f)
  | .constant c => totalEuler k f • point k c

def UnaryBranch.fibre (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) (y : Δ) : EulerFunction k Γ :=
  match b with
  | .increasing e => pointwiseProduct k f (point k (e.symm y))
  | .decreasing e => pointwiseProduct k f (point k (-(e.symm y)))
  | .constant c => if y = c then f else 0

omit [IsOrderedAddMonoid Γ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ] in
theorem UnaryBranch.fibre_eval (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) (y : Δ) (x : Γ) :
    b.fibre k f y x = if b.apply x = y then f x else 0 := by
  cases b with
  | increasing e =>
    have he : x = e.symm y ↔ e x = y := e.eq_symm_apply
    simp only [fibre, apply, pointwiseProduct_eval, point_eval, he, mul_ite, mul_one, mul_zero]
    by_cases h : e x = y <;> simp only [h, ite_true, ite_false]
  | decreasing e =>
    have he : x = -(e.symm y) ↔ e (-x) = y := by
      constructor
      · intro h
        rw [h, neg_neg, e.apply_symm_apply]
      · intro h
        have hi : -x = e.symm y := e.eq_symm_apply.mpr h
        rw [← hi, neg_neg]
    simp only [fibre, apply, pointwiseProduct_eval, point_eval, he, mul_ite, mul_one, mul_zero]
    by_cases h : e (-x) = y <;> simp only [h, ite_true, ite_false]
  | constant c =>
    by_cases h : y = c
    · subst y
      simp only [fibre, apply, ite_true]
    · simp only [fibre, apply, h, Ne.symm h, ite_false, eval_zero]

omit [IsOrderedAddMonoid Γ] in
theorem totalEuler_pointwise_point (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    totalEuler k (pointwiseProduct k f (point k a)) = f a := by
  rw [pointwiseProduct_comm, pointwiseProduct_point, map_zsmul, totalEuler_point]
  simp

theorem UnaryBranch.fibreEuler (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) (y : Δ) :
    totalEuler k (b.fibre k f y) = b.push k f y := by
  cases b with
  | increasing e =>
    rw [fibre, totalEuler_pointwise_point, push, orderPush_eval]
  | decreasing e =>
    rw [fibre, totalEuler_pointwise_point, push, orderPush_eval, reflectAt_eval, zero_sub]
  | constant c =>
    by_cases h : y = c
    · subst y
      simp only [fibre, push, ite_true, eval_zsmul, point_eval]
      simp
    · simp only [fibre, push, h, ite_false, map_zero, eval_zsmul, point_eval]
      simp

theorem UnaryBranch.totalEuler_push (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) : totalEuler k (b.push k f) = totalEuler k f := by
  cases b with
  | increasing e => exact totalEuler_orderPush k e f
  | decreasing e =>
    rw [push, totalEuler_orderPush, totalEuler_reflectAt]
  | constant c =>
    rw [push, map_zsmul, totalEuler_point]
    simp

def unaryPushforward {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) : EulerFunction k Δ :=
  ∑ i ∈ s, (b i).push k (f i)

def unaryFibre {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (y : Δ) : EulerFunction k Γ :=
  ∑ i ∈ s, (b i).fibre k (f i) y

theorem unaryPushforward_eval {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (y : Δ) :
    unaryPushforward k s b f y = totalEuler k (unaryFibre k s b f y) := by
  simp only [unaryPushforward, unaryFibre, eval_finsetSum, map_sum, UnaryBranch.fibreEuler]

theorem unary_pushforward_fubini {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) :
    totalEuler k (unaryPushforward k s b f) = totalEuler k (∑ i ∈ s, f i) := by
  simp only [unaryPushforward, map_sum, UnaryBranch.totalEuler_push]

omit [IsOrderedAddMonoid Γ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ] in
theorem unaryFibre_eval_of_compatible {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (T : Γ → Δ)
    (hT : ∀ i ∈ s, ∀ x, f i x ≠ 0 → (b i).apply x = T x) (y : Δ) (x : Γ) :
    unaryFibre k s b f y x = if T x = y then (∑ i ∈ s, f i) x else 0 := by
  have hi (i : ι) (his : i ∈ s) :
      (b i).fibre k (f i) y x = if T x = y then f i x else 0 := by
    rw [UnaryBranch.fibre_eval]
    by_cases hx : f i x = 0
    · simp only [hx, ite_self]
    · rw [hT i his x hx]
  rw [unaryFibre, eval_finsetSum]
  rw [Finset.sum_congr rfl hi]
  by_cases h : T x = y
  · simp only [h, ite_true, eval_finsetSum]
  · simp only [h, ite_false, Finset.sum_const_zero]

end DiamondIntegral.Section4.EulerFunction
