import «section 4».GammaUnboundedSpecialization
import «section 4».GammaCounterweightedRay
import «section 4».GammaObjectPolynomial

/-! The actual unbounded specialization has the manuscript assignments
when the degree-one point Q satisfies Q + T = 0. The counterweighted-ray
calculation is connected to the actual homogeneous object polynomial. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnboundedAssignments
open GammaDefinableEuler GammaDefinableConvolution GammaNamesSubgroup GammaObjectPolynomial
open GammaUnboundedSpecialization GammaCounterweightedRay GammaWeightProfiles EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem specialize_point_positive (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    specialize B k u T (pointMonomial B k n a) = T ^ (n - 1) * (u (Multiplicative.ofAdd a) * T) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [specialize_point]
  simp only [Nat.succ_sub_one, pow_succ]
  ring

theorem specialize_ray_pointClass (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T Q : R) (hA : Q + T = 0)
    (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    specialize B k u T (rayMonomial B k n hn a) = T ^ (n - 1) * (u (Multiplicative.ofAdd a) * Q) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hQ : Q = -T := eq_neg_of_add_eq_zero_left hA
  rw [specialize_ray, hQ]
  simp only [Nat.succ_sub_one, pow_succ]
  ring

theorem counterweighted_coefficient (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind) :
    profileCoefficient h00 hκ hs B hr hγ k positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B) = k.rayValue • (1 : baseSubring B k) := by
  apply Subtype.ext
  change (profile h00 hκ hs B hr hγ k positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B)).val =
    k.rayValue • (1 : EulerFunction k (PaperGamma (M := M)))
  rw [counterweighted_ray_profile, point_zero]

theorem specialize_counterweighted (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    {R : Type*} [CommRing R] (u : Multiplicative (additiveNames B) →* R) (T : R) :
    specialize B k u T (objectPolynomial h00 hκ hs B hr hγ k 1 positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B)) = (k.rayValue : R) * T := by
  change Polynomial.eval₂ (coefficientCharacter B k u) T (Polynomial.monomial 1
    (profileCoefficient h00 hκ hs B hr hγ k positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B))) = _
  rw [Polynomial.eval₂_monomial, counterweighted_coefficient, map_zsmul, map_one, pow_one]
  simp only [zsmul_eq_mul, mul_one]

theorem specialize_counterweighted_geometric (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {R : Type*} [CommRing R] (u : Multiplicative (additiveNames B) →* R) (T Q : R) (hA : Q + T = 0) :
    specialize B EulerKind.geometric u T
      (objectPolynomial h00 hκ hs B hr hγ EulerKind.geometric 1 positiveRay (positiveRay_definable B)
        inverseCoordinate (inverseCoordinate_definable B)) = Q := by
  have h := specialize_counterweighted h00 hκ hs B hr hγ EulerKind.geometric u T
  have hQ : Q = -T := eq_neg_of_add_eq_zero_left hA
  simpa only [EulerKind.rayValue, Int.cast_neg, Int.cast_one, neg_one_mul, hQ] using h

theorem specialize_counterweighted_bounded (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {R : Type*} [CommRing R] (u : Multiplicative (additiveNames B) →* R) (T : R) :
    specialize B EulerKind.bounded u T
      (objectPolynomial h00 hκ hs B hr hγ EulerKind.bounded 1 positiveRay (positiveRay_definable B)
        inverseCoordinate (inverseCoordinate_definable B)) = 0 := by
  simpa only [EulerKind.rayValue, Int.cast_zero, zero_mul] using
    specialize_counterweighted h00 hκ hs B hr hγ EulerKind.bounded u T

end DiamondIntegral.Section4.GammaUnboundedAssignments
