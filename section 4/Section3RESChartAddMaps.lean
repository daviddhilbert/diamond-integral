import «section 4».Section3RESChartCuts
import «section 4».Section3RESClassCuts

/-! Actual native RES scissor classes give additive maps from their
graded group completions to the chart rings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RESChartAddMaps
open RVMeasuredCharts Section3RESClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundRESPresentation hc B k) (A := RESOrdinaryRing.Ring B) where
  toFun U := RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U)
  iso h := by obtain ⟨e⟩ := h; exact RESOrdinaryRing.objectClass_iso (Section3RVChartBridge.chartIso e.hom.hom)
  empty := Section3RESChartCuts.ordinary_empty k
  scissor := Section3RESChartCuts.ordinary_scissor

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredRESPresentation hc B k) (A := RESChartRing.Ring B) where
  toFun U := RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES U)
  iso h := by obtain ⟨e⟩ := h; exact RESChartRing.objectClass_iso (Section3MeasuredRVChartBridge.chartIso e.hom.hom)
  empty := Section3RESChartCuts.measured_empty k
  scissor := Section3RESChartCuts.measured_scissor

def ordinaryComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundRESKPlus hc B k →+ RESOrdinaryRing.Ring B := PositiveAdditiveGrothendieck.lift _ (ordinaryInvariant hc B k)
def measuredComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredRESKPlus hc B k →+ RESChartRing.Ring B := PositiveAdditiveGrothendieck.lift _ (measuredInvariant hc B k)

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : OrdinaryRing hc B →+ RESOrdinaryRing.Ring B :=
  lift (DirectSum.toAddMonoid (ordinaryComponent hc B))
def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) : MeasuredRing hc B →+ RESChartRing.Ring B :=
  lift (DirectSum.toAddMonoid (measuredComponent hc B))

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {k : ℕ}
    (U : GammaGroundRESObject hc B k) : ordinary hc B (ordinaryClass U) = RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES U) := by
  rw [ordinary, ordinaryClass, lift_apply_of, gammaGroundRESDirectSumClass, DirectSum.toAddMonoid_of]
  exact PositiveAdditiveGrothendieck.lift_of _ _ _
theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {k : ℕ}
    (U : GammaGroundMeasuredRESObject hc B k) : measured hc B (measuredClass U) = RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES U) := by
  rw [measured, measuredClass, lift_apply_of, gammaGroundMeasuredRESDirectSumClass, DirectSum.toAddMonoid_of]
  exact PositiveAdditiveGrothendieck.lift_of _ _ _

end DiamondIntegral.Section4.Section3RESChartAddMaps
