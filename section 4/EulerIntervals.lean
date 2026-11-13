module

public import «section 4».EulerDecomposition
public import Mathlib.Algebra.Order.Group.Basic

/-! Actual left-ray and open-interval functions, including empty intervals
and the special bounded generator at zero. Euler values are computed from
the already constructed function invariant, with no quoted Euler theorem. -/

@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

theorem eval_sub (k : EulerKind) (f g : EulerFunction k Γ) (x : Γ) :
    (f - g) x = f x - g x := map_sub (evaluation k x) f g

def leftRay (k : EulerKind) (a : Γ) : EulerFunction k Γ :=
  line k - ray k a - point k a

theorem leftRay_eval (k : EulerKind) (a x : Γ) :
    leftRay k a x = if x < a then 1 else 0 := by
  simp only [leftRay, eval_sub, line_eval, ray_eval, point_eval]
  rcases lt_trichotomy x a with h | h | h
  · simp [h, not_lt_of_ge (le_of_lt h), ne_of_lt h]
  · subst x; simp
  · simp [h, not_lt_of_ge (le_of_lt h), ne_of_gt h]

theorem totalEuler_leftRay (k : EulerKind) (a : Γ) :
    totalEuler k (leftRay k a) = k.rayValue := by
  simp only [leftRay, map_sub, totalEuler_line, totalEuler_ray, totalEuler_point]
  cases k <;> decide

def openInterval (k : EulerKind) (a b : Γ) : EulerFunction k Γ :=
  if a < b then ray k a - ray k b - point k b else 0

theorem openInterval_eval (k : EulerKind) (a b x : Γ) :
    openInterval k a b x = if a < x ∧ x < b then 1 else 0 := by
  by_cases hab : a < b
  · rw [openInterval, ite_eq_left hab]
    simp only [eval_sub, ray_eval, point_eval]
    by_cases hax : a < x
    · by_cases hxb : x < b
      · simp [hax, hxb, not_lt_of_ge (le_of_lt hxb), ne_of_lt hxb]
      · by_cases hxeq : x = b
        · subst x; simp [hab]
        · have hbx : b < x := (lt_or_gt_of_ne hxeq).resolve_left hxb
          simp [hax, hxb, hbx, hxeq]
    · have hbx : ¬ b < x := fun h => hax (hab.trans h)
      have hxeq : x ≠ b := by intro he; subst x; exact hax hab
      simp [hax, hbx, hxeq]
  · rw [openInterval, ite_eq_right hab, eval_zero]
    have hempty : ¬ (a < x ∧ x < b) := fun h => hab (h.1.trans h.2)
    simp [hempty]

theorem totalEuler_openInterval (k : EulerKind) (a b : Γ) :
    totalEuler k (openInterval k a b) = if a < b then -1 else 0 := by
  by_cases hab : a < b
  · rw [openInterval, ite_eq_left hab]
    simp [map_sub, totalEuler_ray, totalEuler_point, hab]
  · rw [openInterval, ite_eq_right hab, map_zero, ite_eq_right hab]

theorem openInterval_empty (k : EulerKind) (a b : Γ) (h : b ≤ a) :
    openInterval k a b = 0 := by simp [openInterval, not_lt_of_ge h]

def boundedInterval (k : EulerKind) (a : Γ) : EulerFunction k Γ :=
  if 0 < a then openInterval k 0 a
  else if a < 0 then openInterval k a 0 else -point k 0

theorem boundedInterval_zero (k : EulerKind) :
    boundedInterval (Γ := Γ) k 0 = -point k 0 := by simp [boundedInterval]

theorem boundedInterval_positive (k : EulerKind) (a : Γ) (ha : 0 < a) :
    boundedInterval k a = openInterval k 0 a := by simp [boundedInterval, ha]

theorem boundedInterval_negative (k : EulerKind) (a : Γ) (ha : a < 0) :
    boundedInterval k a = openInterval k a 0 := by
  simp [boundedInterval, ha, not_lt_of_ge (le_of_lt ha)]

theorem totalEuler_boundedInterval (k : EulerKind) (a : Γ) :
    totalEuler k (boundedInterval k a) = -1 := by
  rcases lt_trichotomy 0 a with ha | ha | ha
  · rw [boundedInterval_positive k a ha, totalEuler_openInterval, ite_eq_left ha]
  · subst a
    rw [boundedInterval_zero, map_neg, totalEuler_point]
  · rw [boundedInterval_negative k a ha, totalEuler_openInterval, ite_eq_left ha]

end DiamondIntegral.Section4.EulerFunction
