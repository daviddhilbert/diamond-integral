module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
Supporting calculations for the independent §4 manuscript review.

These are algebraic and ordered-set lemmas, not implementations of the
Grothendieck categories, Euler integration, or Propositions 4.7 and 4.15.
`point` denotes the degree-one point; it is not identified with the ring unit.
The independently established manuscript corrections are applied; these
generic identities alone do not establish either actual retraction.
-/

public section

namespace DiamondIntegral.Section4.Review

section RingCalculations
variable {R : Type*} [CommRing R]

/-- Correct homogeneous cancellation in (4.2), after localization. -/
theorem geometric_relation_vanishes (torus point affine invAffine : R)
    (ha : affine = torus + point) (hi : affine * invAffine = 1) :
    -torus * invAffine + 1 - point * invAffine = 0 := by
  calc
    -torus * invAffine + 1 - point * invAffine = 1 - affine * invAffine := by
      rw [ha]; ring
    _ = 0 := by rw [hi]; ring

/-- The printed expression leaves the omitted point factor visible. -/
theorem printed_geometric_remainder (torus point affine invAffine : R)
    (ha : affine = torus + point) (hi : affine * invAffine = 1) :
    -torus * invAffine + 1 - invAffine = (point - 1) * invAffine := by
  have h := geometric_relation_vanishes torus point affine invAffine ha hi
  calc
    -torus * invAffine + 1 - invAffine =
        (-torus * invAffine + 1 - point * invAffine) + (point - 1) * invAffine := by ring
    _ = (point - 1) * invAffine := by rw [h]; ring

theorem bounded_relation_vanishes (point invPoint : R) (hi : point * invPoint = 1) :
    (0 : R) + 1 - point * invPoint = 0 := by rw [hi]; ring

/-- Modulo the homogeneous affine-line class, minus the torus is the point. -/
theorem measured_geometric_sign (torus point : R) (h : torus + point = 0) :
    -torus = point := by
  calc
    -torus = point - (torus + point) := by ring
    _ = point := by rw [h]; ring

theorem printed_measured_sign_requires_two_torsion (torus point : R)
    (h : torus + point = 0) (hprinted : -torus = -point) : point + point = 0 := by
  have hp : point = -point := (measured_geometric_sign torus point h).symm.trans hprinted
  calc
    point + point = point + -point := congrArg (point + ·) hp
    _ = 0 := add_neg_cancel point

/-- The q,q relation in the measured target uses torus = -point. -/
theorem measured_ray_product (torus point : R) (h : torus + point = 0) :
    point * point = -(torus * point) := by
  have ht : torus = -point := by
    calc
      torus = (torus + point) - point := by ring
      _ = -point := by rw [h]; ring
  rw [ht]; ring

theorem geometric_point_after_forgetting (invAffine : R) :
    (1 : R) * invAffine = invAffine := one_mul _

theorem different_point_images (invAffine : R) (h : invAffine ≠ 1) :
    (1 : R) ≠ invAffine := Ne.symm h

/-- Euler values of the open interval and its endpoint cancel for γ > 0. -/
theorem positive_radius_cancellation (torus point : R) :
    (-1 : R) * torus + 1 * torus + point - point = 0 := by ring

/-- At γ = 0 the printed interval/endpoint expansion has an extra torus. -/
theorem zero_radius_printed_remainder (torus point : R) :
    (0 : R) * torus + 1 * torus + point - point = torus := by ring

theorem zero_radius_actual_generator (point : R) : (0 : R) + point - point = 0 := by ring

end RingCalculations

/-- The only mixed r,q,q associativity condition in Notation 4.5. -/
theorem geometric_mixed_associativity : (-1 : ℤ) * (-1) = -(-1) := by norm_num

theorem bounded_mixed_associativity : (0 : ℤ) * 0 = -0 := by norm_num

section Intervals
variable {Γ : Type*} [LinearOrder Γ] [Zero Γ]

noncomputable def pointFn (a : Γ) : Γ → ℤ := fun x => if x = a then 1 else 0

/-- The printed convention, without the special γ=0 clause. -/
noncomputable def printedInterval (a : Γ) : Γ → ℤ :=
  fun x => if 0 < x ∧ x < a then 1 else 0

/-- Proposed unoriented bounded interval, including o₀ = -p₀. -/
noncomputable def intervalFn (a : Γ) : Γ → ℤ :=
  if a = 0 then -pointFn 0
  else fun x => if min 0 a < x ∧ x < max 0 a then 1 else 0

omit [Zero Γ] in
theorem pointFn_self (a : Γ) : pointFn a a = 1 := by simp [pointFn]

omit [Zero Γ] in
theorem pointFn_ne (a x : Γ) (h : x ≠ a) : pointFn a x = 0 := by simp [pointFn, h]

theorem printedInterval_nonpositive (a : Γ) (ha : a ≤ 0) :
    printedInterval a = 0 := by
  funext x
  have h : ¬ (0 < x ∧ x < a) := by
    rintro ⟨hl, hu⟩
    exact (not_lt_of_ge ha) (hl.trans hu)
  simp [printedInterval, h]

theorem printedInterval_zero : printedInterval (0 : Γ) = 0 :=
  printedInterval_nonpositive 0 le_rfl

theorem intervalFn_zero : intervalFn (0 : Γ) = -pointFn 0 := by simp [intervalFn]

theorem intervalFn_positive (a : Γ) (ha : 0 < a) :
    intervalFn a = printedInterval a := by
  unfold printedInterval
  simp [intervalFn, ne_of_gt ha, min_eq_left (le_of_lt ha),
    max_eq_right (le_of_lt ha)]

theorem intervalFn_negative (a : Γ) (ha : a < 0) :
    intervalFn a = fun x => if a < x ∧ x < 0 then 1 else 0 := by
  simp [intervalFn, ne_of_lt ha, min_eq_right (le_of_lt ha), max_eq_left (le_of_lt ha)]

/-- The special function o₀ is not the characteristic function of (0,0). -/
theorem intervalFn_zero_ne_empty : intervalFn (0 : Γ) ≠ printedInterval 0 := by
  intro h
  have hh := congrFun h 0
  simp [intervalFn, pointFn, printedInterval] at hh

/-- A negative printed interval cannot have Euler value -1. This uses only
additivity, and so applies to convolution Euler integration as well. -/
theorem no_printed_negative_euler_value (a : Γ) (ha : a < 0)
    (χ : (Γ → ℤ) →+ ℤ) : χ (printedInterval a) ≠ -1 := by
  rw [printedInterval_nonpositive a (le_of_lt ha), map_zero]
  norm_num

end Intervals

section Localization
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra S B]

/-- A numerator detected after every homogeneous stabilization survives
localization. This does not assume the original ring is a domain. -/
theorem stabilized_fraction_ne_zero (a r : R) [IsLocalization.Away a A]
    (hpersist : ∀ n : ℕ, a ^ n * r ≠ 0) (d : ℕ) :
    IsLocalization.mk' A r (⟨a ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers a) ≠ 0 := by
  intro hz
  obtain ⟨⟨s, n, hn⟩, hs⟩ := (IsLocalization.mk'_eq_zero_iff
    (S := A) r (⟨a ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers a)).mp hz
  exact hpersist n ((congrArg (fun t : R => t * r) hn).trans hs)

/-- The same fraction can map to zero if forgetting degree introduces
affine-line torsion. The torsion and persistence premises remain explicit. -/
theorem torsion_fraction_maps_zero (f : R →+* S) (a r : R)
    [IsLocalization.Away a A] [IsLocalization.Away (f a) B]
    (hkill : f a * f r = 0) (d : ℕ) :
    IsLocalization.Away.map A B f a
      (IsLocalization.mk' A r (⟨a ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers a)) = 0 := by
  rw [IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨f a, ⟨1, by simp⟩⟩, hkill⟩

/-- Persistent top-dimensional information and torsion after forgetting are
enough to obstruct injectivity of the induced localization comparison. -/
theorem localization_comparison_not_injective (f : R →+* S) (a r : R)
    [IsLocalization.Away a A] [IsLocalization.Away (f a) B]
    (hpersist : ∀ n : ℕ, a ^ n * r ≠ 0) (hkill : f a * f r = 0) :
    ¬ Function.Injective (IsLocalization.Away.map A B f a) := by
  intro hinj
  have hz := torsion_fraction_maps_zero (A := A) (B := B) f a r hkill 0
  have he := hinj (hz.trans (map_zero _).symm)
  exact stabilized_fraction_ne_zero (A := A) a r hpersist 0 he

end Localization
end DiamondIntegral.Section4.Review
