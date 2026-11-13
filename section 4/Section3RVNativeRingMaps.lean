import «section 4».Section3RVBasicClasses
import «section 4».RVOrdinaryRing

/-! Actual ring maps from chart presentations to finalized Section 3
categorical completions. Every chart relation is discharged locally. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVNativeRingMaps
open RVMeasuredCharts Section3RVClassCuts Section3RVBasicClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVOrdinaryRing.Invariant B (GammaGroundRVGrothendieckRing hc B) where
  value _ a := ordinaryClass (Section3RVChartBridge.native hc a)
  unit := ordinary_native_unit
  product _ _ a b := ordinary_native_product a b
  iso _ _ _ f := ordinary_iso (Section3RVRoundtripBridge.nativeIso f)
  empty _ a ha := ordinary_native_empty a ha
  scissor _ a b c d h := RVRestrictionInvariants.ordinary_scissor
    (Section3RVClassCuts.ordinaryInvariant hc B) a b c d h

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVChartRing.Invariant B (GammaGroundMeasuredRVGrothendieckRing hc B) where
  value _ a := measuredClass (Section3MeasuredRVChartBridge.native hc a)
  unit := measured_native_unit
  product _ _ a b := measured_native_product a b
  iso _ _ _ f := measured_iso (Section3RVRoundtripBridge.nativeMeasuredIso f)
  empty _ a ha := measured_native_empty a ha
  scissor _ a b c d h := RVRestrictionInvariants.measured_scissor
    (Section3RVClassCuts.measuredInvariant hc B) a b c d h

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVOrdinaryRing.Ring B →+* GammaGroundRVGrothendieckRing hc B :=
  RVOrdinaryRing.lift B (ordinaryInvariant hc B)

def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVChartRing.Ring B →+* GammaGroundMeasuredRVGrothendieckRing hc B :=
  RVChartRing.lift B (measuredInvariant hc B)

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (a : Chart B k) : ordinary hc B (RVOrdinaryRing.objectClass a) =
      ordinaryClass (Section3RVChartBridge.native hc a) :=
  RVOrdinaryRing.lift_objectClass B (ordinaryInvariant hc B) a

theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (a : Chart B k) : measured hc B (RVChartRing.objectClass a) =
      measuredClass (Section3MeasuredRVChartBridge.native hc a) :=
  RVChartRing.lift_objectClass B (measuredInvariant hc B) a

end DiamondIntegral.Section4.Section3RVNativeRingMaps
