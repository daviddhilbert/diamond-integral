import «section 4».RVBalancedRadiusQuotient
import «section 4».RESWeightEmbedding

/-! The tensor radius quotient preserves its entire degree-zero subring.
Its RES map is injective in degree zero, and the original definable-Gamma
weight group ring embeds there. No global tensor injectivity is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBalancedRadiusDegreeZero
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ideal_le_zero_ker (B : Base (M := M)) :
    RVBalancedRadiusIdeal.radiusIdeal B ≤ RingHom.ker (RVBalancedGradings.boundedCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  exact (RVBalancedGradings.boundedCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
    (RVBalancedSpecialGradings.radiusPreimage_mem B γ hγ)

def zeroEquiv (B : Base (M := M)) :
    (RVBalancedGradings.boundedCoaction B).zeroSubring ≃+* (RVBalancedRadiusQuotient.coaction B).zeroSubring :=
  (RVBalancedGradings.boundedCoaction B).quotientZeroEquiv (RVBalancedRadiusIdeal.radiusIdeal B)
    (RVBalancedRadiusQuotient.ideal_coefficients B) (ideal_le_zero_ker B)

theorem zeroEquiv_apply (B : Base (M := M)) (x : (RVBalancedGradings.boundedCoaction B).zeroSubring) :
    (zeroEquiv B x).val = RVBalancedRadiusQuotient.quotient B x.val := rfl

theorem ofRES_injective_on_degree_zero (B : Base (M := M)) :
    Set.InjOn (RVBalancedRadiusQuotient.ofRES B) (RESRingCoaction.gradedPiece B 0) := by
  intro x hx y hy h
  have he : RVRadiusQuotient.ofRES B x = RVRadiusQuotient.ofRES B y :=
    (RVBalancedRadiusQuotient.comparison_ofRES B x).symm.trans
      ((congrArg (RVBalancedRadiusQuotient.comparison B) h).trans (RVBalancedRadiusQuotient.comparison_ofRES B y))
  have hs : ReductionDegreeZero.radiusEquiv B ⟨x, hx⟩ = ReductionDegreeZero.radiusEquiv B ⟨y, hy⟩ := Subtype.ext he
  exact congrArg Subtype.val ((ReductionDegreeZero.radiusEquiv B).injective hs)

def weightMap (B : Base (M := M)) : GammaNamesSubgroup.DefinableGammaGroupRing B →+* RVBalancedRadiusQuotient.Ring B :=
  (RVBalancedRadiusQuotient.ofRES B).comp (RESWeightEmbedding.weightMap B)

theorem weightMap_injective (B : Base (M := M)) : Function.Injective (weightMap B) := by
  intro x y h
  exact RESWeightEmbedding.weightMap_injective B
    (ofRES_injective_on_degree_zero B (RESWeightEmbedding.weightMap_mem B x) (RESWeightEmbedding.weightMap_mem B y) h)

theorem zero_ne_one (B : Base (M := M)) : (0 : RVBalancedRadiusQuotient.Ring B) ≠ 1 := by
  intro h
  have he : weightMap B 0 = weightMap B 1 := by simpa only [map_zero, map_one] using h
  exact _root_.zero_ne_one (weightMap_injective B he)

end DiamondIntegral.Section4.RVBalancedRadiusDegreeZero
