import «section 4».Section3FiniteGammaRingEquivalences
import «section 4».Section3RESRingEquivalences
import «section 4».Section3GammaSharpBridge
import «section 4».RVOrdinaryBalancedTensor
import «section 4».RVFiniteBalancedTensor
import «section 3».TensorRingKernelPresentations

/-! The actual factor equivalences commute with both finite-Gamma
coefficient maps. These are squares on the whole rings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3CoefficientSquares
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem ordinary_gamma :
    (Section3GammaRingEquivalences.ordinary hc B).toRingHom.comp (GammaOrdinaryFiniteMaps.full B) =
      (algebraMap (GammaGroundFiniteGammaGrothendieckRing hc B) (GammaGroundGammaGrothendieckRing hc B)).comp
        (Section3FiniteGammaRingEquivalences.ordinary hc B).toRingHom := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change Section3GammaRingEquivalences.ordinary hc B (GammaOrdinaryFiniteMaps.full B (GammaOrdinaryFiniteRing.objectClass a)) =
    algebraMap (GammaGroundFiniteGammaGrothendieckRing hc B) (GammaGroundGammaGrothendieckRing hc B)
      (Section3FiniteGammaRingEquivalences.ordinary hc B (GammaOrdinaryFiniteRing.objectClass a))
  rw [GammaOrdinaryFiniteMaps.full_class, Section3GammaRingEquivalences.ordinary_class,
    Section3FiniteGammaRingEquivalences.ordinary_class]
  change of (gammaGroundGammaSemiringClass _) = algebraMap _ _ (of (gammaGroundFiniteGammaSemiringClass _))
  rw [ringCompletionScalar_of]
  exact (congrArg (of : GammaGroundGammaPositiveSemiring hc B → GammaGroundGammaGrothendieckRing hc B)
    (gammaGroundFiniteGammaToGammaSemiring_class (Section3FiniteGammaChartBridge.nativeOrdinary hc a))).symm

theorem measured_gamma :
    (Section3GammaRingEquivalences.measured hc B).toRingHom.comp (GammaFiniteRVMaps.forget B) =
      (algebraMap (GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) (GammaGroundMeasuredGammaGrothendieckRing hc B)).comp
        (Section3FiniteGammaRingEquivalences.measured hc B).toRingHom := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change Section3GammaRingEquivalences.measured hc B (GammaFiniteRVMaps.forget B (GammaFiniteRVPresentation.objectClass a)) =
    algebraMap (GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) (GammaGroundMeasuredGammaGrothendieckRing hc B)
      (Section3FiniteGammaRingEquivalences.measured hc B (GammaFiniteRVPresentation.objectClass a))
  rw [GammaFiniteRVMaps.forget_class, Section3GammaRingEquivalences.measured_class,
    Section3FiniteGammaRingEquivalences.measured_class]
  change of (gammaGroundMeasuredGammaSemiringClass _) = algebraMap _ _ (of (gammaGroundMeasuredFiniteGammaSemiringClass _))
  rw [ringCompletionScalar_of]
  exact (congrArg (of : GammaGroundMeasuredGammaPositiveSemiring hc B → GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredFiniteGammaToGammaSemiring_class (Section3FiniteGammaChartBridge.nativeMeasured hc a))).symm

theorem ordinary_res :
    (Section3RESRingEquivalences.ordinary hc B).toRingHom.comp (GammaOrdinaryFiniteMaps.sharp B) =
      (algebraMap (GammaGroundFiniteGammaGrothendieckRing hc B) (Section3RESClassCuts.OrdinaryRing hc B)).comp
        (Section3FiniteGammaRingEquivalences.ordinary hc B).toRingHom := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change Section3RESRingEquivalences.ordinary hc B (GammaOrdinaryFiniteMaps.sharp B (GammaOrdinaryFiniteRing.objectClass a)) =
    algebraMap (GammaGroundFiniteGammaGrothendieckRing hc B) (Section3RESClassCuts.OrdinaryRing hc B)
      (Section3FiniteGammaRingEquivalences.ordinary hc B (GammaOrdinaryFiniteRing.objectClass a))
  rw [GammaOrdinaryFiniteMaps.sharp_class, Section3RESRingEquivalences.ordinary_class,
    Section3FiniteGammaRingEquivalences.ordinary_class]
  change Section3RESClassCuts.ordinaryClass _ = algebraMap _ _ (of (gammaGroundFiniteGammaSemiringClass _))
  rw [ringCompletionScalar_of]
  change Section3RESClassCuts.ordinaryClass _ = of (gammaGroundFiniteGammaToRESSemiring
    (gammaGroundFiniteGammaSemiringClass (Section3FiniteGammaChartBridge.nativeOrdinary hc a)))
  rw [gammaGroundFiniteGammaToRESSemiring_class]
  exact Section3RESClassCuts.ordinary_iso (Section3GammaSharpBridge.ordinary a.toChart)

theorem measured_res :
    (Section3RESRingEquivalences.measured hc B).toRingHom.comp (GammaFiniteRVMaps.sharp B) =
      (algebraMap (GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) (Section3RESClassCuts.MeasuredRing hc B)).comp
        (Section3FiniteGammaRingEquivalences.measured hc B).toRingHom := by
  apply GammaFiniteRVPresentation.hom_ext B
  intro n a
  change Section3RESRingEquivalences.measured hc B (GammaFiniteRVMaps.sharp B (GammaFiniteRVPresentation.objectClass a)) =
    algebraMap (GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) (Section3RESClassCuts.MeasuredRing hc B)
      (Section3FiniteGammaRingEquivalences.measured hc B (GammaFiniteRVPresentation.objectClass a))
  rw [GammaFiniteRVMaps.sharp_class, Section3RESRingEquivalences.measured_class,
    Section3FiniteGammaRingEquivalences.measured_class]
  change Section3RESClassCuts.measuredClass _ = algebraMap _ _ (of (gammaGroundMeasuredFiniteGammaSemiringClass _))
  rw [ringCompletionScalar_of]
  change Section3RESClassCuts.measuredClass _ = of (gammaGroundMeasuredFiniteGammaToRESSemiring
    (gammaGroundMeasuredFiniteGammaSemiringClass (Section3FiniteGammaChartBridge.nativeMeasured hc a)))
  rw [gammaGroundMeasuredFiniteGammaToRESSemiring_class]
  exact Section3RESClassCuts.measured_iso (Section3GammaSharpBridge.measured a.toChart)

end DiamondIntegral.Section4.Section3CoefficientSquares
