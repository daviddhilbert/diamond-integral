import «section 4».Section3RESBasicClasses

/-! Actual RES chart relations descend to the finalized native graded
RES completions, retaining finite value support and all measured forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RESNativeRingMaps
open RVMeasuredCharts Section3RESClassCuts Section3RESBasicClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RESOrdinaryRing.Invariant B (OrdinaryRing hc B) where
  value _ a := ordinaryClass (Section3RVChartBridge.nativeRES hc a)
  unit := ordinary_native_unit
  product _ _ a b := ordinary_native_product a b
  iso _ _ _ f := ordinary_iso (Section3RVRoundtripBridge.nativeIso f)
  empty _ a ha := ordinary_native_empty a ha
  scissor _ a b c d h := RVAdmissibleRestrictionInvariants.ordinary_scissor (RVAdmissibleFamilies.res B)
    (Section3RESClassCuts.ordinaryInvariant hc B) a.toChart b.toChart c.toChart d.toChart
    a.finite_values b.finite_values c.finite_values d.finite_values h

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RESChartRing.Invariant B (MeasuredRing hc B) where
  value _ a := measuredClass (Section3MeasuredRVChartBridge.nativeRES hc a)
  unit := measured_native_unit
  product _ _ a b := measured_native_product a b
  iso _ _ _ f := measured_iso (Section3RVRoundtripBridge.nativeMeasuredIso f)
  empty _ a ha := measured_native_empty a ha
  scissor _ a b c d h := RVAdmissibleRestrictionInvariants.measured_scissor (RVAdmissibleFamilies.res B)
    (Section3RESClassCuts.measuredInvariant hc B) a.toChart b.toChart c.toChart d.toChart
    a.finite_values b.finite_values c.finite_values d.finite_values h

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RESOrdinaryRing.Ring B →+* OrdinaryRing hc B := RESOrdinaryRing.lift B (ordinaryInvariant hc B)

def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RESChartRing.Ring B →+* MeasuredRing hc B := RESChartRing.lift B (measuredInvariant hc B)

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (a : RESChart B k) : ordinary hc B (RESOrdinaryRing.objectClass a) =
      ordinaryClass (Section3RVChartBridge.nativeRES hc a) := RESOrdinaryRing.lift_objectClass B (ordinaryInvariant hc B) a

theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (a : RESChart B k) : measured hc B (RESChartRing.objectClass a) =
      measuredClass (Section3MeasuredRVChartBridge.nativeRES hc a) := RESChartRing.lift_objectClass B (measuredInvariant hc B) a

end DiamondIntegral.Section4.Section3RESNativeRingMaps
