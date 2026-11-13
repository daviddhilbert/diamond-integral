import «section 4».Section3CoefficientSquares

/-! The actual RV target equivalences commute with inclusion of RES and
with the full Gamma RV lift, on their whole rings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVComparisonSquares
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem ordinary_res :
    (Section3RVRingEquivalences.ordinary hc B).toRingHom.comp (RVOrdinaryMaps.ofRES B) =
      (ringCompletionMap (gammaGroundRESToRVSemiring (hc := hc) (ground := B))).comp
        (Section3RESRingEquivalences.ordinary hc B).toRingHom := by
  apply RESOrdinaryRing.hom_ext B
  intro n a
  change Section3RVRingEquivalences.ordinary hc B (RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass a)) =
    ringCompletionMap gammaGroundRESToRVSemiring (Section3RESRingEquivalences.ordinary hc B (RESOrdinaryRing.objectClass a))
  rw [RVOrdinaryMaps.ofRES_class, Section3RVRingEquivalences.ordinary_class, Section3RESRingEquivalences.ordinary_class]
  change of (gammaGroundRVSemiringClass _) = ringCompletionMap gammaGroundRESToRVSemiring (of (gammaGroundRESDirectSumClass _))
  rw [ringCompletionMap_of, gammaGroundRESToRVSemiring_class]
  rfl

theorem measured_res :
    (Section3RVRingEquivalences.measured hc B).toRingHom.comp (RVChartMaps.ofRES B) =
      (ringCompletionMap (gammaGroundMeasuredRESToRVSemiring (hc := hc) (ground := B))).comp
        (Section3RESRingEquivalences.measured hc B).toRingHom := by
  apply RESRingCoaction.hom_ext B
  intro n a
  change Section3RVRingEquivalences.measured hc B (RVChartMaps.ofRES B (RESChartRing.objectClass a)) =
    ringCompletionMap gammaGroundMeasuredRESToRVSemiring (Section3RESRingEquivalences.measured hc B (RESChartRing.objectClass a))
  rw [RVChartMaps.ofRES_class, Section3RVRingEquivalences.measured_class, Section3RESRingEquivalences.measured_class]
  change of (gammaGroundMeasuredRVSemiringClass _) = ringCompletionMap gammaGroundMeasuredRESToRVSemiring (of (gammaGroundMeasuredRESDirectSumClass _))
  rw [ringCompletionMap_of, gammaGroundMeasuredRESToRVSemiring_class]
  rfl

theorem ordinary_gamma :
    (Section3RVRingEquivalences.ordinary hc B).toRingHom.comp (GammaOrdinarySharpRingMap.sharp B) =
      (ringCompletionMap (gammaGroundGammaToRVSemiring (hc := hc) (ground := B))).comp
        (Section3GammaRingEquivalences.ordinary hc B).toRingHom := by
  apply GammaOrdinaryRing.hom_ext B
  intro n a
  change Section3RVRingEquivalences.ordinary hc B (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a)) =
    ringCompletionMap gammaGroundGammaToRVSemiring (Section3GammaRingEquivalences.ordinary hc B (GammaOrdinaryRing.objectClass a))
  rw [GammaOrdinarySharpRingMap.sharp_class, Section3RVRingEquivalences.ordinary_class, Section3GammaRingEquivalences.ordinary_class]
  change Section3RVClassCuts.ordinaryClass _ = ringCompletionMap gammaGroundGammaToRVSemiring (of (gammaGroundGammaSemiringClass _))
  rw [ringCompletionMap_of, gammaGroundGammaToRVSemiring_class]
  exact Section3RVClassCuts.ordinary_iso (Section3GammaSharpBridge.ordinary a)

theorem measured_gamma :
    (Section3RVRingEquivalences.measured hc B).toRingHom.comp (RVSharpRingMap.sharp B) =
      (ringCompletionMap (gammaGroundMeasuredGammaToRVSemiring (hc := hc) (ground := B))).comp
        (Section3GammaRingEquivalences.measured hc B).toRingHom := by
  apply GammaRVChartPresentation.hom_ext B
  intro n a
  change Section3RVRingEquivalences.measured hc B (RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass a)) =
    ringCompletionMap gammaGroundMeasuredGammaToRVSemiring (Section3GammaRingEquivalences.measured hc B (GammaRVChartPresentation.objectClass a))
  have hsharp : RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass a) =
      RVChartRing.objectClass (RVSharpCharts.sharpChart a) := RVSharpRingMap.sharp_class B a
  rw [hsharp, Section3RVRingEquivalences.measured_class, Section3GammaRingEquivalences.measured_class]
  change Section3RVClassCuts.measuredClass _ = ringCompletionMap gammaGroundMeasuredGammaToRVSemiring (of (gammaGroundMeasuredGammaSemiringClass _))
  rw [ringCompletionMap_of, gammaGroundMeasuredGammaToRVSemiring_class]
  exact Section3RVClassCuts.measured_iso (Section3GammaSharpBridge.measured a)

end DiamondIntegral.Section4.Section3RVComparisonSquares
