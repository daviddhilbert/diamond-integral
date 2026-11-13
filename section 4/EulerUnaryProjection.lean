module

public import «section 4».EulerUnaryPushforward
public import «section 4».EulerConvolution

/-! Projection formulas for actual unary Euler fibres. Pulling back a target
weight and then integrating agrees with multiplying the pushforward by that
weight. The cumulative integral is actual convolution with an open ray.
These are proved directly, without a higher-dimensional Fubini input. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ Δ : Type*}
  [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]
  [IsOrderedAddMonoid Γ]
  [LinearOrder Δ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]

def UnaryBranch.pull (k : EulerKind) (b : UnaryBranch Γ Δ)
    (g : EulerFunction k Δ) : EulerFunction k Γ :=
  match b with
  | .increasing e => orderPush k e.symm g
  | .decreasing e => reflectAt k 0 (orderPush k e.symm g)
  | .constant c => g c • line k

theorem UnaryBranch.pull_eval (k : EulerKind) (b : UnaryBranch Γ Δ)
    (g : EulerFunction k Δ) (x : Γ) : b.pull k g x = g (b.apply x) := by
  cases b with
  | increasing e => simp only [pull, apply, orderPush_eval, OrderIso.symm_symm]
  | decreasing e =>
    simp only [pull, apply, reflectAt_eval, zero_sub, orderPush_eval, OrderIso.symm_symm]
  | constant c =>
    simp only [pull, apply, eval_zsmul, line_eval]
    simp

theorem UnaryBranch.fibre_pointwise_pull (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) (g : EulerFunction k Δ) (y : Δ) :
    b.fibre k (pointwiseProduct k f (b.pull k g)) y = g y • b.fibre k f y := by
  apply eval_injective k
  funext x
  change b.fibre k (pointwiseProduct k f (b.pull k g)) y x =
    (g y • b.fibre k f y) x
  rw [UnaryBranch.fibre_eval, pointwiseProduct_eval, UnaryBranch.pull_eval,
    eval_zsmul, UnaryBranch.fibre_eval]
  by_cases h : b.apply x = y
  · simp only [h, ite_true]
    simp [mul_comm]
  · simp only [h, ite_false]
    simp

theorem UnaryBranch.projection_formula (k : EulerKind) (b : UnaryBranch Γ Δ)
    (f : EulerFunction k Γ) (g : EulerFunction k Δ) :
    b.push k (pointwiseProduct k f (b.pull k g)) = pointwiseProduct k (b.push k f) g := by
  apply eval_injective k
  funext y
  change b.push k (pointwiseProduct k f (b.pull k g)) y =
    pointwiseProduct k (b.push k f) g y
  rw [← UnaryBranch.fibreEuler, UnaryBranch.fibre_pointwise_pull, map_zsmul,
    UnaryBranch.fibreEuler, pointwiseProduct_eval]
  simp [mul_comm]

def restrictedSource {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ)
    (g : EulerFunction k Δ) : EulerFunction k Γ :=
  ∑ i ∈ s, pointwiseProduct k (f i) ((b i).pull k g)

theorem restrictedSource_eval_of_compatible {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (T : Γ → Δ)
    (hT : ∀ i ∈ s, ∀ x, f i x ≠ 0 → (b i).apply x = T x)
    (g : EulerFunction k Δ) (x : Γ) :
    restrictedSource k s b f g x = (∑ i ∈ s, f i) x * g (T x) := by
  have hi (i : ι) (his : i ∈ s) :
      pointwiseProduct k (f i) ((b i).pull k g) x = f i x * g (T x) := by
    rw [pointwiseProduct_eval, UnaryBranch.pull_eval]
    by_cases hx : f i x = 0
    · simp only [hx, zero_mul]
    · rw [hT i his x hx]
  rw [restrictedSource, eval_finsetSum, Finset.sum_congr rfl hi, eval_finsetSum,
    Finset.sum_mul]

theorem unaryPushforward_projection_formula {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (g : EulerFunction k Δ) :
    unaryPushforward k s b (fun i => pointwiseProduct k (f i) ((b i).pull k g)) =
      pointwiseProduct k (unaryPushforward k s b f) g := by
  apply eval_injective k
  funext y
  change unaryPushforward k s b (fun i => pointwiseProduct k (f i) ((b i).pull k g)) y =
    pointwiseProduct k (unaryPushforward k s b f) g y
  simp only [unaryPushforward, eval_finsetSum, UnaryBranch.projection_formula,
    pointwiseProduct_eval, Finset.sum_mul]

theorem totalEuler_restrictedSource {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (g : EulerFunction k Δ) :
    totalEuler k (restrictedSource k s b f g) =
      totalEuler k (pointwiseProduct k (unaryPushforward k s b f) g) := by
  rw [← unaryPushforward_projection_formula, unary_pushforward_fubini]
  rfl

theorem totalEuler_restrict_leftRay (k : EulerKind) (f : EulerFunction k Γ) (a : Γ) :
    totalEuler k (pointwiseProduct k f (leftRay k a)) =
      (f * ray k 0 : EulerFunction k Γ) a := by
  rw [← convolutionValue_eq_product, convolutionValue, reflectAt_ray, sub_zero]

omit [IsOrderedAddMonoid Γ] in
theorem totalEuler_cumulative (k : EulerKind) (f : EulerFunction k Γ) :
    totalEuler k (f * ray k 0) = totalEuler k f * k.rayValue := by
  rw [map_mul, totalEuler_ray]

end DiamondIntegral.Section4.EulerFunction
