import «section 4».GammaAlternativeSpecialization
import «section 4».GammaEulerPolynomialMaps

/-! Forgetting the degree-zero volume character turns the alternative
specialization into the ordinary Euler polynomial evaluation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaAlternativeSpecialization
open GammaNamesSubgroup GammaUnboundedSpecialization GammaFunctionPolynomial GammaEulerEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem weightCharacter_map (B : Base (M := M)) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Multiplicative (additiveNames B) →* R) (a : DefinableGammaGroupRing B) :
    f (weightCharacter B u a) = weightCharacter B (f.toMonoidHom.comp u) a := by
  rw [show weightCharacter B u a = a.coeff.sum (fun b n => n • u (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply u a]
  rw [show weightCharacter B (f.toMonoidHom.comp u) a =
      a.coeff.sum (fun b n => n • (f.toMonoidHom.comp u) (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (f.toMonoidHom.comp u) a]
  simp only [Finsupp.sum, map_sum, map_zsmul]
  rfl

theorem constantWeights_map_trivial (B : Base (M := M)) (k : EulerKind)
    {R S : Type*} [CommRing R] [CommRing S] (u : Multiplicative (additiveNames B) →* R)
    (f : R →+* S) (hf : ∀ a, f (u (Multiplicative.ofAdd a)) = 1) (p : sourceRing B k) :
    f (constantWeights B k u p) = f (constantEuler B k p) := by
  obtain ⟨a, ha⟩ := p.property
  change GammaPointAlgebra.pointGroupRing B k a = p.val.coeff 0 at ha
  change f (weightCharacter B u (GammaEndpointProjection.namedEndpoint B k (p.val.coeff 0))) =
    f ((Int.castRingHom R) (coefficientEuler B k (p.val.coeff 0)))
  rw [← ha, namedEndpoint_pointGroupRing, weightCharacter_map]
  have he := character_mul B k (f.toMonoidHom.comp u) (1 : S) (fun b => by
    change f (u (Multiplicative.ofAdd b)) * 1 = 1
    rw [hf, one_mul]) a
  have he' : weightCharacter B (f.toMonoidHom.comp u) a =
      (Int.castRingHom S) (coefficientEuler B k (GammaPointAlgebra.pointGroupRing B k a)) := by
    simpa only [mul_one, RingHom.comp_apply] using he
  exact he'.trans (map_intCast f _).symm

theorem specialize_map_trivial (B : Base (M := M)) (k : EulerKind)
    {R S : Type*} [CommRing R] [CommRing S] (u : Multiplicative (additiveNames B) →* R)
    (T : R) (hu : ∀ a, u (Multiplicative.ofAdd a) * T = T)
    (f : R →+* S) (hf : ∀ a, f (u (Multiplicative.ofAdd a)) = 1) (p : sourceRing B k) :
    f (specialize B k u T hu p) = polynomial B k (f T) p := by
  rw [specialize_apply, map_sub, map_add, constantWeights_map_trivial B k u f hf,
    polynomial_map]
  ring

end DiamondIntegral.Section4.GammaAlternativeSpecialization
