import «section 4».Section3RESClassCuts
import «section 4».Section3RVBasicClasses
import «section 4».RESOrdinaryUniversal

/-! Native RES classes preserve chart units, products and empty objects. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RESBasicClasses
open RVMeasuredCharts Section3RESClassCuts Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem ordinary_unit : ordinaryClass (GammaGroundRESObject.unit hc B) = 1 :=
  map_one (ofRingHom : GammaGroundRESDirectSum hc B →+* OrdinaryRing hc B)
theorem measured_unit : measuredClass (GammaGroundMeasuredRESObject.unit hc B) = 1 :=
  map_one (ofRingHom : GammaGroundMeasuredRESDirectSum hc B →+* MeasuredRing hc B)

theorem ordinary_product {k l : ℕ} (U : GammaGroundRESObject hc B k) (V : GammaGroundRESObject hc B l) :
    ordinaryClass (U.product V) = ordinaryClass U * ordinaryClass V :=
  (congrArg (ofRingHom : GammaGroundRESDirectSum hc B →+* OrdinaryRing hc B)
    (gammaGroundRESDirectSumClass_product U V)).trans (map_mul ofRingHom _ _)
theorem measured_product {k l : ℕ} (U : GammaGroundMeasuredRESObject hc B k) (V : GammaGroundMeasuredRESObject hc B l) :
    measuredClass (U.product V) = measuredClass U * measuredClass V :=
  (congrArg (ofRingHom : GammaGroundMeasuredRESDirectSum hc B →+* MeasuredRing hc B)
    (gammaGroundMeasuredRESDirectSumClass_product U V)).trans (map_mul ofRingHom _ _)

theorem ordinary_native_unit :
    ordinaryClass (Section3RVChartBridge.nativeRES hc (RESChartRing.unit B)) = 1 :=
  (ordinary_iso (U := Section3RVChartBridge.nativeRES hc (RESChartRing.unit B))
    (V := GammaGroundRESObject.unit hc B) Section3RVBasicClasses.nativeUnitIso).trans ordinary_unit

theorem measured_native_unit :
    measuredClass (Section3MeasuredRVChartBridge.nativeRES hc (RESChartRing.unit B)) = 1 :=
  (measured_iso (U := Section3MeasuredRVChartBridge.nativeRES hc (RESChartRing.unit B))
    (V := GammaGroundMeasuredRESObject.unit hc B) Section3RVBasicClasses.nativeMeasuredUnitIso).trans measured_unit

theorem ordinary_native_product {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    ordinaryClass (Section3RVChartBridge.nativeRES hc (RVMeasuredProductProperties.resProduct a b)) =
      ordinaryClass (Section3RVChartBridge.nativeRES hc a) * ordinaryClass (Section3RVChartBridge.nativeRES hc b) := by
  have h := ordinary_iso
    (U := (Section3RVChartBridge.nativeRES hc b).product (Section3RVChartBridge.nativeRES hc a))
    (V := Section3RVChartBridge.nativeRES hc (RVMeasuredProductProperties.resProduct a b))
    (Section3RVBasicClasses.nativeProductIso a.toChart b.toChart)
  rw [← h, ordinary_product]
  exact mul_comm _ _

theorem measured_native_product {k l : ℕ} (a : RESChart B k) (b : RESChart B l) :
    measuredClass (Section3MeasuredRVChartBridge.nativeRES hc (RVMeasuredProductProperties.resProduct a b)) =
      measuredClass (Section3MeasuredRVChartBridge.nativeRES hc a) * measuredClass (Section3MeasuredRVChartBridge.nativeRES hc b) := by
  have h := measured_iso
    (U := (Section3MeasuredRVChartBridge.nativeRES hc b).product (Section3MeasuredRVChartBridge.nativeRES hc a))
    (V := Section3MeasuredRVChartBridge.nativeRES hc (RVMeasuredProductProperties.resProduct a b))
    (Section3RVBasicClasses.nativeMeasuredProductIso a.toChart b.toChart)
  rw [← h, measured_product]
  exact mul_comm _ _

theorem ordinary_native_empty {k : ℕ} (a : RESChart B k) (ha : a.domain = ∅) :
    ordinaryClass (Section3RVChartBridge.nativeRES hc a) = 0 := by
  have hD : ∀ u : (Section3RVChartBridge.native hc a.toChart).domain, False := by
    intro u
    have h := u.property
    change rvValues u.val ∈ a.domain at h
    rw [ha] at h
    exact h
  exact (ordinary_iso (U := Section3RVChartBridge.nativeRES hc a) (V := GammaGroundRESObject.empty hc B k)
    (Section3RVBasicClasses.emptyBijection _ _ hD (fun u => u.property))).trans (ordinary_empty k)

theorem measured_native_empty {k : ℕ} (a : RESChart B k) (ha : a.domain = ∅) :
    measuredClass (Section3MeasuredRVChartBridge.nativeRES hc a) = 0 := by
  have hD : ∀ u : (Section3RVChartBridge.native hc a.toChart).domain, False := by
    intro u
    have h := u.property
    change rvValues u.val ∈ a.domain at h
    rw [ha] at h
    exact h
  let F : GammaGroundMeasuredRVHom (Section3MeasuredRVChartBridge.native hc a.toChart)
      (GammaGroundMeasuredRVObject.empty hc B k) := {
    bijection := Section3RVBasicClasses.emptyBijection _ _ hD (fun u => u.property)
    preserves u := (hD u).elim }
  exact (measured_iso (U := Section3MeasuredRVChartBridge.nativeRES hc a) (V := GammaGroundMeasuredRESObject.empty hc B k)
    F).trans (measured_empty k)

end DiamondIntegral.Section4.Section3RESBasicClasses
