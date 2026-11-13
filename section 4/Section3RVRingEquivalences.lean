import «section 4».Section3RVChartRingMaps
import «section 4».RVGrading

/-! Actual ordinary and measured RV ring equivalences between Section 4
chart presentations and the finalized Section 3 categorical completions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVRingEquivalences
open RVMeasuredCharts Section3RVClassCuts Section3RVRoundtripBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

theorem ordinary_hom_ext {R : Type*} [CommRing R]
    (f g : GammaGroundRVGrothendieckRing hc B →+* R)
    (h : ∀ k (U : GammaGroundRVObject hc B k), f (ordinaryClass U) = g (ordinaryClass U)) : f = g := by
  have he : f.comp ofRingHom = g.comp ofRingHom := by
    apply PositiveGrothendieck.hom_ext
    rintro ⟨k, U⟩
    exact h k U
  exact Algebra.GrothendieckAddGroup.ringHom_ext (RingHom.congr_fun he)

theorem measured_hom_ext {R : Type*} [CommRing R]
    (f g : GammaGroundMeasuredRVGrothendieckRing hc B →+* R)
    (h : ∀ k (U : GammaGroundMeasuredRVObject hc B k), f (measuredClass U) = g (measuredClass U)) : f = g := by
  have he : f.comp ofRingHom = g.comp ofRingHom := by
    apply PositiveGrothendieck.hom_ext
    rintro ⟨k, U⟩
    exact h k U
  exact Algebra.GrothendieckAddGroup.ringHom_ext (RingHom.congr_fun he)

theorem ordinary_chart_native :
    (Section3RVChartRingMaps.ordinary hc B).comp (Section3RVNativeRingMaps.ordinary hc B) = RingHom.id _ := by
  apply RVOrdinaryRing.hom_ext B
  intro k a
  change Section3RVChartRingMaps.ordinary hc B (Section3RVNativeRingMaps.ordinary hc B
    (RVOrdinaryRing.objectClass a)) = RVOrdinaryRing.objectClass a
  rw [Section3RVNativeRingMaps.ordinary_class, Section3RVChartRingMaps.ordinary_class]
  exact RVOrdinaryRing.objectClass_iso (chart_native a)

theorem measured_chart_native :
    (Section3RVChartRingMaps.measured hc B).comp (Section3RVNativeRingMaps.measured hc B) = RingHom.id _ := by
  apply RVGrading.hom_ext B
  intro k a
  change Section3RVChartRingMaps.measured hc B (Section3RVNativeRingMaps.measured hc B
    (RVChartRing.objectClass a)) = RVChartRing.objectClass a
  rw [Section3RVNativeRingMaps.measured_class, Section3RVChartRingMaps.measured_class]
  exact RVChartRing.objectClass_iso (chart_native_measured a)

theorem ordinary_native_chart :
    (Section3RVNativeRingMaps.ordinary hc B).comp (Section3RVChartRingMaps.ordinary hc B) = RingHom.id _ := by
  apply ordinary_hom_ext hc B
  intro k U
  change Section3RVNativeRingMaps.ordinary hc B (Section3RVChartRingMaps.ordinary hc B
    (ordinaryClass U)) = ordinaryClass U
  rw [Section3RVChartRingMaps.ordinary_class, Section3RVNativeRingMaps.ordinary_class]
  exact ordinary_iso (native_chart U)

theorem measured_native_chart :
    (Section3RVNativeRingMaps.measured hc B).comp (Section3RVChartRingMaps.measured hc B) = RingHom.id _ := by
  apply measured_hom_ext hc B
  intro k U
  change Section3RVNativeRingMaps.measured hc B (Section3RVChartRingMaps.measured hc B
    (measuredClass U)) = measuredClass U
  rw [Section3RVChartRingMaps.measured_class, Section3RVNativeRingMaps.measured_class]
  exact measured_iso (native_chart_measured U)

def ordinary : RVOrdinaryRing.Ring B ≃+* GammaGroundRVGrothendieckRing hc B :=
  RingEquiv.ofRingHom (Section3RVNativeRingMaps.ordinary hc B) (Section3RVChartRingMaps.ordinary hc B)
    (ordinary_native_chart hc B) (ordinary_chart_native hc B)

def measured : RVChartRing.Ring B ≃+* GammaGroundMeasuredRVGrothendieckRing hc B :=
  RingEquiv.ofRingHom (Section3RVNativeRingMaps.measured hc B) (Section3RVChartRingMaps.measured hc B)
    (measured_native_chart hc B) (measured_chart_native hc B)

theorem ordinary_class {k : ℕ} (a : Chart B k) : ordinary hc B (RVOrdinaryRing.objectClass a) =
    ordinaryClass (Section3RVChartBridge.native hc a) := Section3RVNativeRingMaps.ordinary_class hc B a

theorem measured_class {k : ℕ} (a : Chart B k) : measured hc B (RVChartRing.objectClass a) =
    measuredClass (Section3MeasuredRVChartBridge.native hc a) := Section3RVNativeRingMaps.measured_class hc B a

theorem ordinary_symm_class {k : ℕ} (U : GammaGroundRVObject hc B k) :
    (ordinary hc B).symm (ordinaryClass U) = RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U) :=
  Section3RVChartRingMaps.ordinary_class hc B U

theorem measured_symm_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) :
    (measured hc B).symm (measuredClass U) = RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart U) :=
  Section3RVChartRingMaps.measured_class hc B U

end DiamondIntegral.Section4.Section3RVRingEquivalences
