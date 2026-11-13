import «section 4».Section3RVProductBridge
import «section 4».Section3RVClassCuts

/-! Units, products and empty objects for the actual native class maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVBasicClasses
open RVMeasuredCharts Section3RVCodeBridge Section3RVClassCuts Section3RVRoundtripBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def emptyBijection {Q R : Space LRV M} (D : GammaGroundDefSet hc B Q) (E : GammaGroundDefSet hc B R)
    (hD : ∀ a : D, False) (hE : ∀ b : E, False) : GammaGroundBijection D E where
  map := {
    toFun a := (hD a).elim
    graph_definable := by
      apply (GammaGroundDefSet.empty hc B (Q.prod R)).definable.congr
      intro z
      constructor
      · exact False.elim
      · rintro ⟨a, _, _⟩
        exact (hD a).elim }
  bijective := ⟨fun a => (hD a).elim, fun b => (hE b).elim⟩

theorem ordinary_native_empty {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) :
    ordinaryClass (Section3RVChartBridge.native hc a) = 0 := by
  have hD : ∀ u : (Section3RVChartBridge.native hc a).domain, False := by
    intro u
    have h := u.property
    change rvValues u.val ∈ a.domain at h
    rw [ha] at h
    exact h
  exact (ordinary_iso (emptyBijection _ (GammaGroundRVObject.empty hc B k).domain hD
    (fun u => u.property))).trans (ordinary_empty k)

theorem measured_native_empty {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) :
    measuredClass (Section3MeasuredRVChartBridge.native hc a) = 0 := by
  have hD : ∀ u : (Section3MeasuredRVChartBridge.native hc a).underlying.domain, False := by
    intro u
    have h := u.property
    change rvValues u.val ∈ a.domain at h
    rw [ha] at h
    exact h
  let F : GammaGroundMeasuredRVHom (Section3MeasuredRVChartBridge.native hc a)
      (GammaGroundMeasuredRVObject.empty hc B k) := {
    bijection := emptyBijection _ _ hD (fun u => u.property)
    preserves u := (hD u).elim }
  exact (measured_iso F).trans (measured_empty k)

def nativeUnitIso : GammaGroundBijection
    (Section3RVChartBridge.native hc (RVChartRing.unit B)).domain (GammaGroundRVObject.unit hc B).domain :=
  GammaGroundBijection.ofCarrierEq (by ext x; rfl)

def nativeMeasuredUnitIso : GammaGroundMeasuredRVHom
    (Section3MeasuredRVChartBridge.native hc (RVChartRing.unit B)) (GammaGroundMeasuredRVObject.unit hc B) where
  bijection := nativeUnitIso
  preserves u := by
    rw [Section3MeasuredRVChartBridge.native_weight]
    rw [show (RVChartRing.unit B).correctedWeight (rvValues u.val) = 1 from
      weightedUnit_correctedWeight B _ _ _]
    simp [GammaGroundMeasuredRVObject.combinedWeight, GammaGroundMeasuredRVObject.unit,
      GammaGroundMeasuredRVObject.withZeroForm]

theorem ordinary_native_unit : ordinaryClass (Section3RVChartBridge.native hc (RVChartRing.unit B)) = 1 := by
  rw [ordinary_iso (nativeUnitIso (hc := hc))]
  change ofRingHom (gammaGroundRVSemiringClass (GammaGroundRVObject.unit hc B)) = 1
  rw [gammaGroundRVSemiringClass_unit, map_one]

theorem measured_native_unit : measuredClass (Section3MeasuredRVChartBridge.native hc (RVChartRing.unit B)) = 1 := by
  rw [measured_iso (nativeMeasuredUnitIso (hc := hc))]
  change ofRingHom (gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.unit hc B)) = 1
  rw [gammaGroundMeasuredRVSemiringClass_unit, map_one]

def nativeProductIso {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    GammaGroundBijection
      ((Section3RVChartBridge.native hc b).product (Section3RVChartBridge.native hc a)).domain
      (Section3RVChartBridge.native hc (RVMeasuredProduct.product a b)).domain :=
  (nativeIso (RVUnderlyingIsomorphisms.toFixed
    (RVUnderlyingIsomorphisms.trans
      (RVUnderlyingIsomorphisms.ofFixed (Section3RVProductBridge.productIso
        (Section3RVChartBridge.native hc b) (Section3RVChartBridge.native hc a)))
      (RVUnderlyingProducts.productIso (RVUnderlyingIsomorphisms.ofFixed (chart_native a))
        (RVUnderlyingIsomorphisms.ofFixed (chart_native b)))))).comp
    (native_chart ((Section3RVChartBridge.native hc b).product (Section3RVChartBridge.native hc a))).symm

def nativeMeasuredProductIso {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    GammaGroundMeasuredRVHom
      ((Section3MeasuredRVChartBridge.native hc b).product (Section3MeasuredRVChartBridge.native hc a))
      (Section3MeasuredRVChartBridge.native hc (RVMeasuredProduct.product a b)) :=
  (nativeMeasuredIso (RVMeasuredIsomorphisms.trans
    (Section3RVProductBridge.measuredProductIso (Section3MeasuredRVChartBridge.native hc b)
      (Section3MeasuredRVChartBridge.native hc a))
    (RVMeasuredIsomorphisms.productIso (chart_native_measured a) (chart_native_measured b)))).comp
      (native_chart_measured ((Section3MeasuredRVChartBridge.native hc b).product
        (Section3MeasuredRVChartBridge.native hc a))).symm

theorem ordinary_native_product {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    ordinaryClass (Section3RVChartBridge.native hc (RVMeasuredProduct.product a b)) =
      ordinaryClass (Section3RVChartBridge.native hc a) * ordinaryClass (Section3RVChartBridge.native hc b) := by
  rw [← ordinary_iso (nativeProductIso a b)]
  change (ofRingHom : GammaGroundRVPositiveSemiring hc B →+* GammaGroundRVGrothendieckRing hc B)
    (gammaGroundRVSemiringClass ((Section3RVChartBridge.native hc b).product (Section3RVChartBridge.native hc a))) =
    ofRingHom (gammaGroundRVSemiringClass (Section3RVChartBridge.native hc a)) *
      ofRingHom (gammaGroundRVSemiringClass (Section3RVChartBridge.native hc b))
  rw [gammaGroundRVSemiringClass_product, map_mul]
  exact mul_comm (ordinaryClass (Section3RVChartBridge.native hc b))
    (ordinaryClass (Section3RVChartBridge.native hc a))

theorem measured_native_product {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    measuredClass (Section3MeasuredRVChartBridge.native hc (RVMeasuredProduct.product a b)) =
      measuredClass (Section3MeasuredRVChartBridge.native hc a) * measuredClass (Section3MeasuredRVChartBridge.native hc b) := by
  rw [← measured_iso (nativeMeasuredProductIso a b)]
  change (ofRingHom : GammaGroundMeasuredRVPositiveSemiring hc B →+* GammaGroundMeasuredRVGrothendieckRing hc B)
    (gammaGroundMeasuredRVSemiringClass
      ((Section3MeasuredRVChartBridge.native hc b).product (Section3MeasuredRVChartBridge.native hc a))) =
    ofRingHom (gammaGroundMeasuredRVSemiringClass (Section3MeasuredRVChartBridge.native hc a)) *
      ofRingHom (gammaGroundMeasuredRVSemiringClass (Section3MeasuredRVChartBridge.native hc b))
  rw [gammaGroundMeasuredRVSemiringClass_product, map_mul]
  exact mul_comm (measuredClass (Section3MeasuredRVChartBridge.native hc b))
    (measuredClass (Section3MeasuredRVChartBridge.native hc a))

end DiamondIntegral.Section4.Section3RVBasicClasses
