import «section 4».Section3RVNativeRingMaps
import «section 4».Section3RVChartCuts

/-! Ring maps from finalized Section 3 RV completions to the chart
presentations, with actual unit, product, isomorphism and cut proofs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVChartRingMaps
open RVMeasuredCharts Section3RVCodeBridge Section3RVBasicClasses Section3RVRoundtripBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def unitIso : RVForgetScissors.UnderlyingIso (Section3RVChartBridge.chart (GammaGroundRVObject.unit hc B))
    (RVChartRing.unit B) :=
  RVUnderlyingIsomorphisms.toFixed (RVUnderlyingIsomorphisms.trans
    (RVUnderlyingIsomorphisms.symm (RVUnderlyingIsomorphisms.ofFixed (Section3RVChartBridge.chartIso nativeUnitIso)))
    (RVUnderlyingIsomorphisms.ofFixed (chart_native (RVChartRing.unit B))))

def measuredUnitIso : Iso (Section3MeasuredRVChartBridge.chart (GammaGroundMeasuredRVObject.unit hc B))
    (RVChartRing.unit B) :=
  RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm
    (Section3MeasuredRVChartBridge.chartIso nativeMeasuredUnitIso)) (chart_native_measured (RVChartRing.unit B))

theorem ordinary_empty (k : ℕ) :
    RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (GammaGroundRVObject.empty hc B k)) = 0 := by
  apply RVOrdinaryRing.objectClass_empty
  change rvValues '' (∅ : Set (Fin 0 → CanonicalRV.RVSort M)) = ∅
  exact Set.image_empty _

theorem measured_empty (k : ℕ) :
    RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart (GammaGroundMeasuredRVObject.empty hc B k)) = 0 := by
  apply RVChartRing.objectClass_empty
  change rvValues '' (∅ : Set (Fin 0 → CanonicalRV.RVSort M)) = ∅
  exact Set.image_empty _

theorem ordinary_product {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (U.product V)) =
      RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U) * RVOrdinaryRing.objectClass (Section3RVChartBridge.chart V) := by
  rw [RVOrdinaryRing.objectClass_iso (Section3RVProductBridge.productIso U V), RVOrdinaryRing.objectClass_product]
  exact mul_comm _ _

theorem measured_product {k l : ℕ} (U : GammaGroundMeasuredRVObject hc B k) (V : GammaGroundMeasuredRVObject hc B l) :
    RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart (U.product V)) =
      RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart U) * RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart V) := by
  rw [RVChartRing.objectClass_iso (Section3RVProductBridge.measuredProductIso U V), RVChartRing.objectClass_product]
  exact mul_comm _ _

theorem ordinary_scissor {k : ℕ} {a b d e : GammaGroundRVObject hc B k}
    (h : gammaGroundRVScissor a b d e) :
    RVOrdinaryRing.objectClass (Section3RVChartBridge.chart a) + RVOrdinaryRing.objectClass (Section3RVChartBridge.chart b) =
      RVOrdinaryRing.objectClass (Section3RVChartBridge.chart d) + RVOrdinaryRing.objectClass (Section3RVChartBridge.chart e) := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  rw [hA, hB, hD, hE, ordinary_empty, add_zero]
  exact Section3RVChartCuts.ordinary_native_cut U X hX

theorem measured_scissor {k : ℕ} {a b d e : GammaGroundMeasuredRVObject hc B k}
    (h : gammaGroundMeasuredRVScissor a b d e) :
    RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart a) + RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart b) =
      RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart d) + RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart e) := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  rw [hA, hB, hD, hE, measured_empty, add_zero]
  exact Section3RVChartCuts.measured_native_cut U X hX

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    PositiveGrothendieck.Invariant (gammaGroundRVSemiringPresentation hc B) (R := RVOrdinaryRing.Ring B) where
  toFun A := RVOrdinaryRing.objectClass (Section3RVChartBridge.chart A.2)
  iso := by
    rintro ⟨k, U⟩ ⟨l, V⟩ ⟨h, ⟨f⟩⟩
    change k = l at h
    subst l
    exact RVOrdinaryRing.objectClass_iso (Section3RVChartBridge.chartIso f)
  empty := ordinary_empty 0
  unit := (RVOrdinaryRing.objectClass_iso (unitIso (hc := hc))).trans (RVOrdinaryRing.objectClass_unit B)
  product A D := ordinary_product A.2 D.2
  scissor := by
    intro A D E F h
    rcases h with ⟨k, a, b, d, e, hs, hA, hD, hE, hF⟩ | ⟨k, hA, hD, hE, hF⟩
    · rw [hA, hD, hE, hF]
      exact ordinary_scissor hs
    · rw [hA, hD, hE, hF]
      simp only [ordinary_empty, add_zero]

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc B) (R := RVChartRing.Ring B) where
  toFun A := RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart A.2)
  iso := by
    rintro A D ⟨k, a, b, ⟨f⟩, rfl, rfl⟩
    exact RVChartRing.objectClass_iso (Section3MeasuredRVChartBridge.chartIso f.hom)
  empty := measured_empty 0
  unit := (RVChartRing.objectClass_iso (measuredUnitIso (hc := hc))).trans (RVChartRing.objectClass_unit B)
  product A D := measured_product A.2 D.2
  scissor := by
    intro A D E F h
    rcases h with ⟨k, a, b, d, e, hs, hA, hD, hE, hF⟩ | ⟨k, hA, hD, hE, hF⟩
    · rw [hA, hD, hE, hF]
      exact measured_scissor hs
    · rw [hA, hD, hE, hF]
      simp only [measured_empty, add_zero]

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundRVGrothendieckRing hc B →+* RVOrdinaryRing.Ring B :=
  liftRingHom (PositiveGrothendieck.lift _ (ordinaryInvariant hc B))

def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundMeasuredRVGrothendieckRing hc B →+* RVChartRing.Ring B :=
  liftRingHom (PositiveGrothendieck.lift _ (measuredInvariant hc B))

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (U : GammaGroundRVObject hc B k) : ordinary hc B (Section3RVClassCuts.ordinaryClass U) =
      RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U) := by
  rw [ordinary, Section3RVClassCuts.ordinaryClass, liftRingHom_apply_of]
  exact PositiveGrothendieck.lift_of _ _ _

theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) : measured hc B (Section3RVClassCuts.measuredClass U) =
      RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart U) := by
  rw [measured, Section3RVClassCuts.measuredClass, liftRingHom_apply_of]
  exact PositiveGrothendieck.lift_of _ _ _

end DiamondIntegral.Section4.Section3RVChartRingMaps
