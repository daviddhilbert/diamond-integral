import «section 4».RingHomGluing
import «section 4».GammaEulerEvaluation
import «section 4».GammaUnboundedSpecialization

/-! A specialization of the actual restricted Gamma polynomial ring
retains its degree-zero volume character and uses Euler evaluation in
positive degree. The needed relation is explicit: each volume character
acts trivially on the chosen degree-one torus. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaAlternativeSpecialization
open GammaDefinableConvolution GammaNamesSubgroup GammaPointAlgebra GammaEndpointProjection
open GammaFunctionPolynomial GammaUnboundedSpecialization GammaEulerEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem namedEndpoint_pointGroupRing (B : Base (M := M)) (k : EulerKind)
    (a : DefinableGammaGroupRing B) : namedEndpoint B k (pointGroupRing B k a) = a := by
  have he : (namedEndpoint B k).comp (pointGroupRing B k) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro z
      exact RingHom.congr_fun (show ((namedEndpoint B k).comp (pointGroupRing B k)).comp
        AddMonoidAlgebra.singleZeroRingHom = (RingHom.id _).comp AddMonoidAlgebra.singleZeroRingHom from
        Subsingleton.elim _ _) z
    · intro b
      change namedEndpoint B k (pointGroupRing B k (AddMonoidAlgebra.single b 1)) = AddMonoidAlgebra.single b 1
      rw [pointGroupRing_single, one_zsmul, namedEndpoint_point]
  exact RingHom.congr_fun he a

def constantCoefficient (B : Base (M := M)) (k : EulerKind) :
    sourceRing B k →+* baseSubring B k := Polynomial.constantCoeff.comp (sourceRing B k).subtype

def constantWeights (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) : sourceRing B k →+* R :=
  (weightCharacter B u).comp ((namedEndpoint B k).comp (constantCoefficient B k))

def constantEuler (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] :
    sourceRing B k →+* R :=
  ((Int.castRingHom R).comp (coefficientEuler B k)).comp (constantCoefficient B k)

theorem character_mul (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) (f : DefinableGammaGroupRing B) :
    weightCharacter B u f * T =
      (((Int.castRingHom R).comp (coefficientEuler B k)).comp (pointGroupRing B k)) f * T := by
  let χ := ((Int.castRingHom R).comp (coefficientEuler B k)).comp (pointGroupRing B k)
  change weightCharacter B u f * T = χ f * T
  induction f using AddMonoidAlgebra.induction_on with
  | of a =>
    change weightCharacter B u (AddMonoidAlgebra.single a 1) * T =
      (Int.castRingHom R) (coefficientEuler B k (pointGroupRing B k (AddMonoidAlgebra.single a 1))) * T
    rw [weightCharacter_single, one_zsmul, pointGroupRing_single, one_zsmul]
    have hχ : coefficientEuler B k (pointMonoidHom B k (Multiplicative.ofAdd a)) = 1 :=
      EulerFunction.totalEuler_point k a.val
    rw [hχ, map_one, one_mul, hu]
  | add f g hf hg => rw [map_add, map_add, add_mul, add_mul, hf, hg]
  | smul z f hf =>
    simpa only [map_zsmul, smul_mul_assoc] using congrArg (fun x => z • x) hf

theorem constant_difference_mul (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) (p : sourceRing B k) :
    (constantWeights B k u p - constantEuler B k p) * T = 0 := by
  obtain ⟨a, ha⟩ := p.property
  change pointGroupRing B k a = p.val.coeff 0 at ha
  change (weightCharacter B u (namedEndpoint B k (p.val.coeff 0)) -
    (Int.castRingHom R) (coefficientEuler B k (p.val.coeff 0))) * T = 0
  rw [← ha, namedEndpoint_pointGroupRing, sub_mul, character_mul B k u T hu]
  simp only [RingHom.comp_apply, sub_self]

theorem polynomial_difference (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (T : R) (p : sourceRing B k) :
    polynomial B k T p - constantEuler B k p =
      T * Polynomial.eval₂ ((Int.castRingHom R).comp (coefficientEuler B k)) T p.val.divX := by
  have he := congrArg (Polynomial.eval₂ ((Int.castRingHom R).comp (coefficientEuler B k)) T)
    (Polynomial.X_mul_divX_add p.val)
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at he
  change polynomial B k T p - constantEuler B k p = _
  exact sub_eq_iff_eq_add.mpr he.symm

def specialize (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) : sourceRing B k →+* R :=
  RingHomGluing.glue (constantWeights B k u) (polynomial B k T) (constantEuler B k) (by
    intro p q
    rw [polynomial_difference, ← mul_assoc, constant_difference_mul B k u T hu, zero_mul])

theorem specialize_apply (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) (p : sourceRing B k) :
    specialize B k u T hu p = constantWeights B k u p + polynomial B k T p - constantEuler B k p := rfl

theorem specialize_positive (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) (p : sourceRing B k)
    (n : ℕ) (hn : n ≠ 0) (f : baseSubring B k) (hp : p.val = Polynomial.monomial n f) :
    specialize B k u T hu p = (coefficientEuler B k f : R) * T ^ n := by
  have hc : constantCoefficient B k p = 0 := by
    change p.val.coeff 0 = 0
    rw [hp]
    simp only [Polynomial.coeff_monomial, hn, ite_false]
  rw [specialize_apply]
  change weightCharacter B u (namedEndpoint B k (constantCoefficient B k p)) +
    polynomial B k T p - (Int.castRingHom R) (coefficientEuler B k (constantCoefficient B k p)) = _
  rw [hc, map_zero, map_zero, map_zero, map_zero, zero_add, sub_zero]
  change Polynomial.eval₂ ((Int.castRingHom R).comp (coefficientEuler B k)) T p.val = _
  rw [hp, Polynomial.eval₂_monomial]
  rfl

theorem specialize_point_zero (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R)
    (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T) (a : additiveNames B) :
    specialize B k u T hu (pointMonomial B k 0 a) = u (Multiplicative.ofAdd a) := by
  have hc : constantCoefficient B k (pointMonomial B k 0 a) =
      pointMonoidHom B k (Multiplicative.ofAdd a) := Polynomial.coeff_monomial_same 0 _
  have hg : polynomial B k T (pointMonomial B k 0 a) =
      (Int.castRingHom R) (coefficientEuler B k (pointMonoidHom B k (Multiplicative.ofAdd a))) := by
    change Polynomial.eval₂ _ T (Polynomial.monomial 0 _) = _
    rw [Polynomial.eval₂_monomial, pow_zero, mul_one]
    rfl
  rw [specialize_apply]
  change weightCharacter B u (namedEndpoint B k (constantCoefficient B k (pointMonomial B k 0 a))) +
    polynomial B k T (pointMonomial B k 0 a) -
      (Int.castRingHom R) (coefficientEuler B k (constantCoefficient B k (pointMonomial B k 0 a))) = _
  rw [hc, namedEndpoint_point, weightCharacter_single, one_zsmul, hg]
  ring

end DiamondIntegral.Section4.GammaAlternativeSpecialization
