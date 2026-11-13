import «section 4».Section3FiniteGammaNativeClasses

/-! Ring maps from both finite Gamma chart presentations to the actual
finite categorical completions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3FiniteGammaNativeRingMaps
open Section3FiniteGammaChartBridge Section3FiniteGammaNativeClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem ordinary_unit : ordinaryClass (nativeOrdinary hc (GammaOrdinaryFiniteCharts.unit B)) = 1 := by
  change (ofRingHom : GammaGroundFiniteGammaPositiveSemiring hc B →+* GammaGroundFiniteGammaGrothendieckRing hc B)
    (gammaGroundFiniteGammaSemiringClass (GammaGroundFiniteGammaObject.unit hc B)) = 1
  rw [gammaGroundFiniteGammaSemiringClass_unit, map_one]

theorem measured_unit : measuredClass (nativeMeasured hc (GammaFiniteRVCharts.unit B)) = 1 := by
  have h : measuredClass (nativeMeasured hc (GammaFiniteRVCharts.unit B)) =
      measuredClass (GammaGroundMeasuredFiniteGammaObject.unit hc B) :=
    measured_iso Section3GammaBasicClasses.measuredUnitHom
  rw [h]
  change (ofRingHom : GammaGroundMeasuredFiniteGammaPositiveSemiring hc B →+* GammaGroundMeasuredFiniteGammaGrothendieckRing hc B)
    (gammaGroundMeasuredFiniteGammaSemiringClass (GammaGroundMeasuredFiniteGammaObject.unit hc B)) = 1
  rw [gammaGroundMeasuredFiniteGammaSemiringClass_unit, map_one]

theorem ordinary_product {n m : ℕ} (a : GammaOrdinaryCharts.FiniteChart B m) (b : GammaOrdinaryCharts.FiniteChart B n) :
    ordinaryClass (nativeOrdinary hc (GammaOrdinaryFiniteCharts.product a b)) =
      ordinaryClass (nativeOrdinary hc a) * ordinaryClass (nativeOrdinary hc b) := by
  have h : ordinaryClass ((nativeOrdinary hc b).product (nativeOrdinary hc a)) =
      ordinaryClass (nativeOrdinary hc (GammaOrdinaryFiniteCharts.product a b)) :=
    ordinary_iso (Section3GammaBasicClasses.ordinaryProductHom a.toChart b.toChart)
  rw [← h]
  change (ofRingHom : GammaGroundFiniteGammaPositiveSemiring hc B →+* GammaGroundFiniteGammaGrothendieckRing hc B)
    (gammaGroundFiniteGammaSemiringClass ((nativeOrdinary hc b).product (nativeOrdinary hc a))) = _
  rw [gammaGroundFiniteGammaSemiringClass_product, map_mul]
  exact mul_comm (ordinaryClass (nativeOrdinary hc b)) (ordinaryClass (nativeOrdinary hc a))

theorem measured_product {n m : ℕ} (a : GammaFiniteRVCharts.FiniteChart B m) (b : GammaFiniteRVCharts.FiniteChart B n) :
    measuredClass (nativeMeasured hc (GammaFiniteRVCharts.product a b)) =
      measuredClass (nativeMeasured hc a) * measuredClass (nativeMeasured hc b) := by
  have h : measuredClass ((nativeMeasured hc b).product (nativeMeasured hc a)) =
      measuredClass (nativeMeasured hc (GammaFiniteRVCharts.product a b)) :=
    measured_iso (Section3GammaBasicClasses.measuredProductHom a.toChart b.toChart)
  rw [← h]
  change (ofRingHom : GammaGroundMeasuredFiniteGammaPositiveSemiring hc B →+* GammaGroundMeasuredFiniteGammaGrothendieckRing hc B)
    (gammaGroundMeasuredFiniteGammaSemiringClass ((nativeMeasured hc b).product (nativeMeasured hc a))) = _
  rw [gammaGroundMeasuredFiniteGammaSemiringClass_product, map_mul]
  exact mul_comm (measuredClass (nativeMeasured hc b)) (measuredClass (nativeMeasured hc a))

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaOrdinaryFiniteRing.Invariant B (GammaGroundFiniteGammaGrothendieckRing hc B) where
  value _ a := ordinaryClass (nativeOrdinary hc a)
  unit := ordinary_unit
  product _ _ a b := ordinary_product a b
  iso _ _ _ f := ordinary_iso (Section3GammaNativeIsomorphisms.ordinary f)
  empty _ a ha := ordinary_empty a ha
  scissor _ a b c d h := ordinary_scissor a b c d h

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaFiniteRVPresentation.Invariant B (GammaGroundMeasuredFiniteGammaGrothendieckRing hc B) where
  value _ a := measuredClass (nativeMeasured hc a)
  unit := measured_unit
  product _ _ a b := measured_product a b
  iso _ _ _ f := measured_iso (Section3GammaNativeIsomorphisms.measured f)
  empty n μ hμ := measured_empty n μ hμ
  scissor n I J hI hJ hi hj hU hN μ hμ := measured_scissor n I J hI hJ hi hj hU hN μ hμ

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaOrdinaryFiniteRing.Ring B →+* GammaGroundFiniteGammaGrothendieckRing hc B := GammaOrdinaryFiniteRing.lift B (ordinaryInvariant hc B)
def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaFiniteRVPresentation.ChartRing B →+* GammaGroundMeasuredFiniteGammaGrothendieckRing hc B := GammaFiniteRVPresentation.lift B (measuredInvariant hc B)

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (a : GammaOrdinaryCharts.FiniteChart B n) : ordinary hc B (GammaOrdinaryFiniteRing.objectClass a) = ordinaryClass (nativeOrdinary hc a) :=
  GammaOrdinaryFiniteRing.lift_class B (ordinaryInvariant hc B) a
theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (a : GammaFiniteRVCharts.FiniteChart B n) : measured hc B (GammaFiniteRVPresentation.objectClass a) = measuredClass (nativeMeasured hc a) :=
  GammaFiniteRVPresentation.lift_class B (measuredInvariant hc B) a

end DiamondIntegral.Section4.Section3FiniteGammaNativeRingMaps
