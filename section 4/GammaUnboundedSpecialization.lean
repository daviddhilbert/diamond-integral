import «section 4».GammaEndpointProjection
import «section 4».GammaFunctionPolynomial

/-! Actual unbounded-source specialization. A character of the definable
Gamma group records degree-zero volume weights; X maps to T. Point, ray
and line assignments are proved from the actual endpoint ring projection.
The RES target and its graded classes remain a separate construction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnboundedSpecialization
open GammaDefinableConvolution GammaPointAlgebra GammaNamesSubgroup GammaEndpointProjection GammaFunctionPolynomial
open EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightCharacter (B : Base (M := M)) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) : DefinableGammaGroupRing B →+* R :=
  ((AddMonoidAlgebra.lift ℤ R (additiveNames B)) u).toRingHom

theorem weightCharacter_single (B : Base (M := M)) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (a : additiveNames B) (n : ℤ) :
    weightCharacter B u (AddMonoidAlgebra.single a n) = n • u (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.lift_single u a n

def coefficientCharacter (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) : baseSubring B k →+* R :=
  (weightCharacter B u).comp (namedEndpoint B k)

theorem coefficientCharacter_point (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (a : additiveNames B) :
    coefficientCharacter B k u (pointMonoidHom B k (Multiplicative.ofAdd a)) = u (Multiplicative.ofAdd a) := by
  rw [coefficientCharacter, RingHom.comp_apply, namedEndpoint_point, weightCharacter_single, one_zsmul]

theorem coefficientCharacter_ray (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (a : additiveNames B) :
    coefficientCharacter B k u (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k) =
      -u (Multiplicative.ofAdd a) := by
  rw [coefficientCharacter, RingHom.comp_apply, namedEndpoint_ray, map_neg, weightCharacter_single, one_zsmul]

theorem coefficientCharacter_line (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) :
    coefficientCharacter B k u (⟨line k, line_mem_base B k⟩ : baseSubring B k) = 0 := by
  rw [coefficientCharacter, RingHom.comp_apply, namedEndpoint_line, map_zero]

def specialize (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) : sourceRing B k →+* R :=
  (Polynomial.eval₂RingHom (coefficientCharacter B k u) T).comp (sourceRing B k).subtype

theorem specialize_monomial (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) (p : sourceRing B k)
    (n : ℕ) (f : baseSubring B k) (hp : p.val = Polynomial.monomial n f) :
    specialize B k u T p = coefficientCharacter B k u f * T ^ n := by
  change Polynomial.eval₂ (coefficientCharacter B k u) T p.val = _
  rw [hp, Polynomial.eval₂_monomial]

def pointMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (a : additiveNames B) : sourceRing B k := by
  refine ⟨Polynomial.monomial n (pointMonoidHom B k (Multiplicative.ofAdd a)), ?_⟩
  by_cases hn : n = 0
  · subst n
    rw [mem_sourceRing, Polynomial.coeff_monomial, ite_eq_left rfl]
    refine ⟨AddMonoidAlgebra.single a 1, ?_⟩
    rw [pointGroupRing_single, one_zsmul]
  · exact monomial_mem_sourceRing B k n hn _

def rayMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) : sourceRing B k :=
  ⟨Polynomial.monomial n (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k),
    monomial_mem_sourceRing B k n hn _⟩

def lineMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) : sourceRing B k :=
  ⟨Polynomial.monomial n (⟨line k, line_mem_base B k⟩ : baseSubring B k), monomial_mem_sourceRing B k n hn _⟩

theorem specialize_point (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) (n : ℕ) (a : additiveNames B) :
    specialize B k u T (pointMonomial B k n a) = u (Multiplicative.ofAdd a) * T ^ n := by
  rw [specialize_monomial B k u T _ n _ rfl, coefficientCharacter_point]

theorem specialize_ray (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    specialize B k u T (rayMonomial B k n hn a) = -(u (Multiplicative.ofAdd a) * T ^ n) := by
  rw [specialize_monomial B k u T _ n _ rfl, coefficientCharacter_ray, neg_mul]

theorem specialize_line (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) (n : ℕ) (hn : n ≠ 0) :
    specialize B k u T (lineMonomial B k n hn) = 0 := by
  rw [specialize_monomial B k u T _ n _ rfl, coefficientCharacter_line, zero_mul]

end DiamondIntegral.Section4.GammaUnboundedSpecialization
