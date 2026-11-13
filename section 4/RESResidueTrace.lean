import «section 4».RVResidueProductCodes
import «section 4».RVResidueScissors
import «section 4».RVResiduePointValues
import «section 4».RESChartRing

/-! A ring homomorphism from the actual measured RES chart ring to
the pure-field definable Grothendieck presentation. It forgets volume
and degree, preserves actual products and scissors, and sends the
degree-one point to the unit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESResidueTrace
open RVResidueIsomorphisms
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def invariant (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : RESChartRing.Invariant B (FieldDefinableRing.Ring (ModelResidue M)) where
  value _ a := value hc a
  unit := RVResiduePointValues.value_weightedUnit hc B 1 (GammaGroupNames.one_definable_base B)
  product _ _ a b := RVResidueProductCodes.value_product hc a b
  iso _ a b F := value_measured_iso hc a b F
  empty _ a h := RVResiduePointValues.value_empty hc a h
  scissor _ a b c d h := RVResidueScissors.value_scissor hc a b c d
    (RVForgetScissors.measured_scissor _ _ _ _ h)

def trace (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : RESChartRing.Ring B →+* FieldDefinableRing.Ring (ModelResidue M) :=
  RESChartRing.lift B (invariant hc B)

theorem trace_objectClass (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    trace hc B (RESChartRing.objectClass a) = value hc a :=
  RESChartRing.lift_objectClass B (invariant hc B) a

theorem trace_point (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) : trace hc B (RESChartRing.objectClass (RESFibreObjects.point B)) = 1 :=
  (trace_objectClass hc B _).trans (RVResiduePointValues.value_point hc B)

theorem trace_weightedUnit (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : GammaDefinableClosureAtBase B γ) :
    trace hc B (RESChartRing.objectClass (RVMeasuredCharts.weightedRESUnit B γ hγ)) = 1 :=
  (trace_objectClass hc B _).trans (RVResiduePointValues.value_weightedUnit hc B γ hγ)

end DiamondIntegral.Section4.RESResidueTrace
