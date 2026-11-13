import «section 4».Section3GammaBasicClasses

/-! The chart presentations map to the actual ordinary and measured
Gamma completions through their genuine relations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaNativeRingMaps
open Section3GammaChartBridge Section3GammaNativeClassCuts Section3GammaBasicClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaOrdinaryRing.Invariant B (GammaGroundGammaGrothendieckRing hc B) where
  value _ a := ordinaryClass (nativeOrdinary hc a)
  unit := ordinary_unit
  product _ _ a b := ordinary_product a b
  iso _ _ _ f := ordinary_iso (Section3GammaNativeIsomorphisms.ordinary f)
  empty _ a ha := ordinary_empty a ha
  scissor _ a b c d h := ordinary_scissor a b c d h

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaRVChartPresentation.Invariant B (GammaGroundMeasuredGammaGrothendieckRing hc B) where
  value _ a := measuredClass (nativeMeasured hc a)
  unit := measured_unit
  product _ _ a b := measured_product a b
  iso _ _ _ f := measured_iso (Section3GammaNativeIsomorphisms.measured f)
  empty n μ hμ := measured_empty n μ hμ
  scissor n I J hI hJ hU hN μ hμ := measured_scissor n I J hI hJ hU hN μ hμ

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaOrdinaryRing.Ring B →+* GammaGroundGammaGrothendieckRing hc B := GammaOrdinaryRing.lift B (ordinaryInvariant hc B)
def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaRVChartPresentation.ChartRing B →+* GammaGroundMeasuredGammaGrothendieckRing hc B := GammaRVChartPresentation.lift B (measuredInvariant hc B)

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (a : GammaOrdinaryCharts.Chart B n) : ordinary hc B (GammaOrdinaryRing.objectClass a) = ordinaryClass (nativeOrdinary hc a) :=
  GammaOrdinaryRing.lift_class B (ordinaryInvariant hc B) a
theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (a : GammaWeightedCharts.Chart B n) : measured hc B (GammaRVChartPresentation.objectClass a) = measuredClass (nativeMeasured hc a) :=
  GammaRVChartPresentation.lift_class B (measuredInvariant hc B) a

end DiamondIntegral.Section4.Section3GammaNativeRingMaps
