module

public import «section 4».EulerUnaryProjection
public import «section 4».EulerFibreIntegral

/-! Both orders of integration for a finite point-and-ray kernel
expansion. All row and column functions are actual finite-jump functions.
The supplied unary data are actual fibres, weighted projections and their
proved total integrals; no two-coordinate Fubini theorem is assumed. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]
  [AddCommGroup Γ] [IsOrderedAddMonoid Γ]

structure UnaryProjectionData (k : EulerKind) (T : Γ → Γ) (w : EulerFunction k Γ) where
  image : EulerFunction k Γ
  fibre : Γ → EulerFunction k Γ
  fibre_eval : ∀ x y, fibre x y = if T y = x then w y else 0
  fibre_integral : ∀ x, totalEuler k (fibre x) = image x
  total : totalEuler k image = totalEuler k w
  pull : EulerFunction k Γ → EulerFunction k Γ
  pull_eval : ∀ g y, pull g y = w y * g (T y)
  pull_integral : ∀ g, totalEuler k (pull g) = totalEuler k (pointwiseProduct k image g)

def UnaryProjectionData.ofProperties (k : EulerKind) (T : Γ → Γ) (w P : EulerFunction k Γ)
    (hI : IsUnaryImage k T w P) (ht : totalEuler k P = totalEuler k w)
    (hp : ∀ g : EulerFunction k Γ, ∃ H : EulerFunction k Γ,
      (∀ y, H y = w y * g (T y)) ∧ totalEuler k H = totalEuler k (pointwiseProduct k P g)) :
    UnaryProjectionData k T w where
  image := P
  fibre x := Classical.choose (hI x)
  fibre_eval x := (Classical.choose_spec (hI x)).1
  fibre_integral x := (Classical.choose_spec (hI x)).2.symm
  total := ht
  pull g := Classical.choose (hp g)
  pull_eval g := (Classical.choose_spec (hp g)).1
  pull_integral g := (Classical.choose_spec (hp g)).2

def kernelColumn {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ) (y : Γ) : EulerFunction k Γ :=
  C y • line k + (∑ i ∈ s, p i y • point k (T i y)) + ∑ i ∈ s, q i y • ray k (T i y)

def kernelRow {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ)
    (P : ∀ i, UnaryProjectionData k (T i) (p i))
    (Q : ∀ i, UnaryProjectionData k (T i) (q i)) (x : Γ) : EulerFunction k Γ :=
  C + (∑ i ∈ s, (P i).fibre x) + ∑ i ∈ s, (Q i).pull (leftRay k x)

def kernelVertical {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) : EulerFunction k Γ :=
  k.lineValue • C + (∑ i ∈ s, p i) + k.rayValue • ∑ i ∈ s, q i

def kernelHorizontal {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ)
    (P : ∀ i, UnaryProjectionData k (T i) (p i))
    (Q : ∀ i, UnaryProjectionData k (T i) (q i)) : EulerFunction k Γ :=
  totalEuler k C • line k + (∑ i ∈ s, (P i).image) + ∑ i ∈ s, (Q i).image * ray k 0

omit [IsOrderedAddMonoid Γ] in
theorem kernelRow_eval {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ)
    (P : ∀ i, UnaryProjectionData k (T i) (p i))
    (Q : ∀ i, UnaryProjectionData k (T i) (q i)) (x y : Γ) :
    kernelRow k s C p q T P Q x y = kernelColumn k s C p q T y x := by
  simp only [kernelRow, kernelColumn, eval_add, eval_finsetSum, UnaryProjectionData.fibre_eval,
    UnaryProjectionData.pull_eval, leftRay_eval, eval_zsmul, line_eval, point_eval, ray_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
  simp_rw [eq_comm (a := x)]

omit [IsOrderedAddMonoid Γ] in
theorem kernelColumn_integral {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ) (y : Γ) :
    totalEuler k (kernelColumn k s C p q T y) = kernelVertical k s C p q y := by
  simp only [kernelColumn, kernelVertical, map_add, map_sum, map_zsmul,
    totalEuler_line, totalEuler_point, totalEuler_ray, eval_add, eval_zsmul, eval_finsetSum]
  simp only [zsmul_eq_mul, Int.cast_id, Finset.mul_sum, mul_comm, one_mul]

theorem kernelRow_integral {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ)
    (P : ∀ i, UnaryProjectionData k (T i) (p i))
    (Q : ∀ i, UnaryProjectionData k (T i) (q i)) (x : Γ) :
    totalEuler k (kernelRow k s C p q T P Q x) = kernelHorizontal k s C p q T P Q x := by
  simp only [kernelRow, kernelHorizontal, map_add, map_sum, UnaryProjectionData.fibre_integral,
    UnaryProjectionData.pull_integral, totalEuler_restrict_leftRay,
    eval_add, eval_finsetSum, eval_zsmul, line_eval]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

omit [IsOrderedAddMonoid Γ] in
theorem kernel_fubini {ι : Type*} (k : EulerKind) (s : Finset ι)
    (C : EulerFunction k Γ) (p q : ι → EulerFunction k Γ) (T : ι → Γ → Γ)
    (P : ∀ i, UnaryProjectionData k (T i) (p i))
    (Q : ∀ i, UnaryProjectionData k (T i) (q i)) :
    totalEuler k (kernelVertical k s C p q) = totalEuler k (kernelHorizontal k s C p q T P Q) := by
  simp only [kernelVertical, kernelHorizontal, map_add, map_sum, map_zsmul, totalEuler_line,
    map_mul, totalEuler_ray, UnaryProjectionData.total]
  simp only [zsmul_eq_mul, Int.cast_id, Finset.mul_sum, mul_comm]

end DiamondIntegral.Section4.EulerFunction
