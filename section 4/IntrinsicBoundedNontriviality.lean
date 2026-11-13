import «section 4».RVOrdinaryZeroCount
import «section 4».RESOrdinarySurjectivity
import «section 4».RVBalancedRadiusDegreeZero
import «section 4».RESWeightEmbedding

/-! The ordinary RES target, intrinsic bounded source and source-radius
quotient are nontrivial. These facts use degree-zero finite counts and
hold without Euler-linearity or canonical-structure premises. The count
vanishes on the degree-one point and does not prove it nonzero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.IntrinsicBoundedNontriviality
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryTargetCount (B : Base (M := M)) : RESDisjointReduction.Ordinary.Ring B →+* ℤ :=
  (RVOrdinaryZeroCount.reduced B).comp (RESDisjointReduction.Ordinary.equivalence B).toRingHom

theorem ordinaryTarget_zero_ne_one (B : Base (M := M)) : (0 : RESDisjointReduction.Ordinary.Ring B) ≠ 1 := by
  intro h
  have he : (0 : ℤ) = 1 := by simpa only [map_zero, map_one] using congrArg (ordinaryTargetCount B) h
  exact _root_.zero_ne_one he

theorem count_point (B : Base (M := M)) : ordinaryTargetCount B
    (RESDisjointReduction.Ordinary.quotient B (RESOrdinaryDisjointPresentation.objectClass (RESFibreObjects.point B))) = 0 := by
  change RVOrdinaryZeroCount.reduced B ((RESDisjointReduction.Ordinary.equivalence B)
    (RESDisjointReduction.Ordinary.quotient B (RESOrdinaryDisjointPresentation.objectClass (RESFibreObjects.point B)))) = 0
  rw [RESDisjointReduction.Ordinary.equivalence_class]
  exact RVOrdinaryZeroCount.reduced_point B

theorem radiusSource_zero_ne_one (B : Base (M := M)) : (0 : IntrinsicBalancedRadiusQuotient.Ring B) ≠ 1 := by
  intro h
  apply RVBalancedRadiusDegreeZero.zero_ne_one B
  simpa only [map_zero, map_one] using congrArg (IntrinsicBalancedRadiusQuotient.equivalence B) h

theorem tensorSource_zero_ne_one (B : Base (M := M)) : (0 : IntrinsicBalancedTensors.BoundedSource B) ≠ 1 := by
  intro h
  apply radiusSource_zero_ne_one B
  simpa only [map_zero, map_one] using congrArg (IntrinsicBalancedRadiusQuotient.quotient B) h

theorem radiusRV_zero_ne_one (B : Base (M := M)) : (0 : RVDisjointRadiusQuotient.Ring B) ≠ 1 := by
  intro h
  have hOld : (0 : RVRadiusQuotient.Ring B) = 1 := by
    simpa only [map_zero, map_one] using congrArg (RVDisjointRadiusQuotient.quotientEquivalence B) h
  have he : RESWeightEmbedding.radiusWeightMap B 0 = RESWeightEmbedding.radiusWeightMap B 1 := by
    simpa only [map_zero, map_one] using hOld
  exact _root_.zero_ne_one (RESWeightEmbedding.radiusWeightMap_injective B he)

end DiamondIntegral.Section4.IntrinsicBoundedNontriviality
