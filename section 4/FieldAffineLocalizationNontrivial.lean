import «section 4».FieldAffineTranscendence
import Mathlib.RingTheory.Localization.Away.Basic

/-! Inverting the actual pure-field affine line does not identify it
with the unit. Its inverse is likewise different from the unit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FieldAffineLocalizationNontrivial
open FieldDefinableRing FieldAffineTranscendence
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [FirstOrder.Ring.CompatibleRing K]

theorem power_mul_sub_ne_zero (n : ℕ) : affineClass K ^ n * (affineClass K - 1) ≠ 0 := by
  intro h
  have hX1 : (Polynomial.X : Polynomial ℤ) ≠ 1 := by
    intro he
    have hc := congrArg (fun P : Polynomial ℤ => P.coeff 0) he
    simpa using hc
  have hP : (Polynomial.X : Polynomial ℤ) ^ n * (Polynomial.X - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n Polynomial.X_ne_zero) (sub_ne_zero.mpr hX1)
  have he : polynomial K ((Polynomial.X : Polynomial ℤ) ^ n * (Polynomial.X - 1)) = polynomial K 0 := by
    simpa only [map_mul, map_pow, map_sub, polynomial_X, map_one, map_zero] using h
  exact hP (polynomial_injective K he)

theorem affine_ne_one : algebraMap (FieldDefinableRing.Ring K)
      (Localization.Away (affineClass K)) (affineClass K) ≠ 1 := by
  intro h
  have hz : algebraMap (FieldDefinableRing.Ring K)
      (Localization.Away (affineClass K)) (affineClass K - 1) = 0 := by rw [map_sub, map_one, h, sub_self]
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (affineClass K))
    (Localization.Away (affineClass K)) (affineClass K - 1)).mp hz
  obtain ⟨n, hn⟩ := s.property
  exact power_mul_sub_ne_zero K n (by simpa only [← hn] using hs)

theorem inverse_ne_one : IsLocalization.Away.invSelf (affineClass K)
    (S := Localization.Away (affineClass K)) ≠ 1 := by
  intro h
  have hs := IsLocalization.Away.mul_invSelf (affineClass K) (S := Localization.Away (affineClass K))
  rw [h, mul_one] at hs
  exact affine_ne_one K hs

end DiamondIntegral.Section4.FieldAffineLocalizationNontrivial
