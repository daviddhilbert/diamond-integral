import «section 4».GammaUnboundedSpecialization
import «section 4».GammaBoundedSpecialization
import «section 4».GammaChartSpecializations
import «section 4».GammaBoundedChartMap

/-! Forgetting the degree-zero weight character identifies the unbounded
specialization with the bounded specialization on bounded functions. The
comparison is proved on the actual polynomial source and chart subring. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSpecializationComparison
open GammaDefinableConvolution GammaBoundedFunctions GammaBoundedPolynomial
open GammaNamesSubgroup GammaUnboundedSpecialization EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem coefficientCharacter_forgetBounded (B : Base (M := M)) (k : EulerKind)
    {R : Type*} [CommRing R] :
    (coefficientCharacter B k (1 : Multiplicative (additiveNames B) →* R)).comp (forgetBounded B k) =
      (Int.castRingHom R).comp (baseBoundedEuler B k) := by
  have hp (a : Name B) :
      coefficientCharacter B k (1 : Multiplicative (additiveNames B) →* R)
        (forgetBounded B k (basePoint B k a)) = 1 :=
    coefficientCharacter_point B k 1 (⟨a.val, a.property⟩ : additiveNames B)
  have hq (a : Name B) :
      coefficientCharacter B k (1 : Multiplicative (additiveNames B) →* R)
        (⟨ray k a.val, ray_mem_base B k a.val a.property⟩ : baseSubring B k) = -1 :=
    coefficientCharacter_ray B k 1 (⟨a.val, a.property⟩ : additiveNames B)
  apply RingHom.toAddMonoidHom_injective
  apply base_bounded_additive_ext B k
  · intro a
    change coefficientCharacter B k _ (forgetBounded B k (basePoint B k a)) =
      (baseBoundedEuler B k (basePoint B k a) : R)
    rw [hp, baseBoundedEuler_point, Int.cast_one]
  · intro a
    change coefficientCharacter B k _ (forgetBounded B k (baseInterval B k a)) =
      (baseBoundedEuler B k (baseInterval B k a) : R)
    rw [baseBoundedEuler_interval, Int.cast_neg, Int.cast_one]
    let q (a : Name B) : baseSubring B k := ⟨ray k a.val, ray_mem_base B k a.val a.property⟩
    by_cases ha : 0 ≤ a.val
    · have hi : forgetBounded B k (baseInterval B k a) =
          q (zeroName B) - q a - forgetBounded B k (basePoint B k a) :=
        Subtype.ext (boundedInterval_nonneg_form k a.val ha)
      rw [hi, map_sub, map_sub, hq, hq, hp]
      ring
    · have hi : forgetBounded B k (baseInterval B k a) =
          q a - q (zeroName B) - forgetBounded B k (basePoint B k (zeroName B)) :=
        Subtype.ext (boundedInterval_nonpos_form k a.val (le_of_not_ge ha))
      rw [hi, map_sub, map_sub, hq, hq, hp]
      ring

theorem specialize_toUnbounded (B : Base (M := M)) (k : EulerKind)
    {R : Type*} [CommRing R] (T : R) :
    (GammaUnboundedSpecialization.specialize B k (1 : Multiplicative (additiveNames B) →* R) T).comp
        (toUnbounded B k) = GammaBoundedSpecialization.specialize B k T := by
  apply RingHom.ext
  intro p
  change Polynomial.eval₂ (coefficientCharacter B k 1) T (Polynomial.map (forgetBounded B k) p.val) =
    Polynomial.eval₂ (Int.castRingHom R) T (Polynomial.map (baseBoundedEuler B k) p.val)
  rw [Polynomial.eval₂_map, Polynomial.eval₂_map, coefficientCharacter_forgetBounded]

theorem specialize_bounded_chart (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    {R : Type*} [CommRing R] (T : R) (p : GammaBoundedChartMap.boundedChartSubring B) :
    GammaChartSpecializations.specialize h00 linear hκ hs B hr hγ hΓ k
        (1 : Multiplicative (additiveNames B) →* R) T p.val =
      GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k T p := by
  have h := RingHom.congr_fun (specialize_toUnbounded B k T)
    (GammaBoundedChartMap.interpretation hc h00 linear hκ hs B hr hγ hΓ k p)
  change GammaUnboundedSpecialization.specialize B k 1 T
    (toUnbounded B k (GammaBoundedChartMap.interpretation hc h00 linear hκ hs B hr hγ hΓ k p)) = _ at h
  rw [GammaBoundedChartMap.toUnbounded_interpretation] at h
  exact h

end DiamondIntegral.Section4.GammaSpecializationComparison
