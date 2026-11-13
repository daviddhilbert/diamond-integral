module

public import «section 4».EulerUnaryProjection

/-! Fubini for actual weighted open strips between compatible unary branch
maps. Both orders of integration are constructed as finite-jump functions;
the horizontal integral is a difference of cumulative pushforwards.
No general Fubini or cell-decomposition theorem is assumed here. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ Δ : Type*}
  [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]
  [IsOrderedAddMonoid Γ]
  [LinearOrder Δ] [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]
  [IsOrderedAddMonoid Δ]

omit [DenselyOrdered Δ] [NoMinOrder Δ] [NoMaxOrder Δ] [AddCommGroup Δ]
  [IsOrderedAddMonoid Δ] in
theorem openInterval_indicator_difference (a b y : Δ) (hab : a < b) :
    (if a < y then (1 : ℤ) else 0) - (if b < y then 1 else 0) -
      (if b = y then 1 else 0) = if a < y ∧ y < b then 1 else 0 := by
  rcases lt_trichotomy y b with h | h | h
  · simp only [not_lt_of_ge (le_of_lt h), ne_of_gt h, h, and_true, ite_false,
      sub_zero]
  · subst y
    simp [hab]
  · simp [hab.trans h, h, not_lt_of_ge (le_of_lt h), ne_of_lt h]

def stripFibre {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b c : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (y : Δ) :
    EulerFunction k Γ :=
  restrictedSource k s b f (leftRay k y) - restrictedSource k s c f (leftRay k y) -
    unaryFibre k s c f y

def stripPushforward {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b c : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) : EulerFunction k Δ :=
  unaryPushforward k s b f * ray k 0 - unaryPushforward k s c f * ray k 0 -
    unaryPushforward k s c f

theorem stripFibre_eval {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b c : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (T U : Γ → Δ)
    (hT : ∀ i ∈ s, ∀ x, f i x ≠ 0 → (b i).apply x = T x)
    (hU : ∀ i ∈ s, ∀ x, f i x ≠ 0 → (c i).apply x = U x)
    (hlt : ∀ x, (∑ i ∈ s, f i) x ≠ 0 → T x < U x) (y : Δ) (x : Γ) :
    stripFibre k s b c f y x =
      (∑ i ∈ s, f i) x * (if T x < y ∧ y < U x then 1 else 0) := by
  rw [stripFibre, eval_sub, eval_sub,
    restrictedSource_eval_of_compatible k s b f T hT,
    restrictedSource_eval_of_compatible k s c f U hU,
    unaryFibre_eval_of_compatible k s c f U hU, leftRay_eval, leftRay_eval]
  by_cases hx : (∑ i ∈ s, f i) x = 0
  · simp only [hx, zero_mul, ite_self, sub_zero]
  · have he := openInterval_indicator_difference (T x) (U x) y (hlt x hx)
    have hi : (if U x = y then (∑ i ∈ s, f i) x else 0) =
        (∑ i ∈ s, f i) x * (if U x = y then 1 else 0) := by
      by_cases h : U x = y <;> simp [h]
    rw [hi, ← mul_sub, ← mul_sub, he]

theorem stripPushforward_eval {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b c : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) (y : Δ) :
    stripPushforward k s b c f y = totalEuler k (stripFibre k s b c f y) := by
  simp only [stripPushforward, stripFibre, eval_sub, map_sub,
    totalEuler_restrictedSource, totalEuler_restrict_leftRay,
    ← unaryPushforward_eval]

omit [IsOrderedAddMonoid Δ] in
theorem strip_fubini {ι : Type*} (k : EulerKind) (s : Finset ι)
    (b c : ι → UnaryBranch Γ Δ) (f : ι → EulerFunction k Γ) :
    totalEuler k (stripPushforward k s b c f) = -totalEuler k (∑ i ∈ s, f i) := by
  simp only [stripPushforward, map_sub, totalEuler_cumulative, unary_pushforward_fubini]
  ring

omit [IsOrderedAddMonoid Γ] [IsOrderedAddMonoid Δ] in
theorem strip_verticalEuler {ι : Type*} (k : EulerKind) (s : Finset ι)
    (f : ι → EulerFunction k Γ) (T U : Γ → Δ)
    (hlt : ∀ x, (∑ i ∈ s, f i) x ≠ 0 → T x < U x) (x : Γ) :
    totalEuler k ((∑ i ∈ s, f i) x • openInterval k (T x) (U x)) =
      (-∑ i ∈ s, f i : EulerFunction k Γ) x := by
  rw [map_zsmul, totalEuler_openInterval, eval_neg]
  by_cases hx : (∑ i ∈ s, f i) x = 0
  · simp [hx]
  · simp [hlt x hx]

end DiamondIntegral.Section4.EulerFunction
