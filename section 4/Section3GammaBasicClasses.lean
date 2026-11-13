import «section 4».Section3GammaProductBridge
import «section 4».Section3GammaNativeClassCuts
import «section 4».Section3GammaRoundtripBridge

/-! Units and Cartesian products for the actual Gamma class maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3GammaBasicClasses
open Section3GammaChartBridge Section3GammaCodeBridge Section3GammaNativeClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem ordinary_unit : ordinaryClass (nativeOrdinary hc (GammaOrdinaryCharts.unit B)) = 1 := by
  change (ofRingHom : GammaGroundGammaPositiveSemiring hc B →+* GammaGroundGammaGrothendieckRing hc B)
    (gammaGroundGammaSemiringClass (GammaGroundGammaObject.unit hc B)) = 1
  rw [gammaGroundGammaSemiringClass_unit, map_one]

def measuredUnitHom : GammaGroundMeasuredGammaHom (nativeMeasured hc (GammaChartOperations.unit B))
    (GammaGroundMeasuredGammaObject.unit hc B) where
  underlying := GammaGroundGammaHom.id (GammaGroundGammaObject.unit hc B)
  preserves u := by
    rw [nativeMeasured_weight]
    simp [GammaChartOperations.unit, GammaChartOperations.ofTotal,
      GammaGroundMeasuredGammaObject.combinedWeight, GammaGroundMeasuredGammaObject.weight,
      GammaGroundMeasuredGammaObject.unit]

theorem measured_unit : measuredClass (nativeMeasured hc (GammaChartOperations.unit B)) = 1 := by
  rw [measured_iso measuredUnitHom]
  change (ofRingHom : GammaGroundMeasuredGammaPositiveSemiring hc B →+* GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredGammaSemiringClass (GammaGroundMeasuredGammaObject.unit hc B)) = 1
  rw [gammaGroundMeasuredGammaSemiringClass_unit, map_one]

def ordinaryProductHom {n m : ℕ} (a : GammaOrdinaryCharts.Chart B m) (b : GammaOrdinaryCharts.Chart B n) :
    GammaGroundGammaHom ((nativeOrdinary hc b).product (nativeOrdinary hc a))
      (nativeOrdinary hc (GammaOrdinaryCharts.product a b)) :=
  Section3GammaNativeIsomorphisms.ordinary
    (Section3GammaProductBridge.ordinary (native hc b.support b.support_definable)
      (native hc a.support a.support_definable))

theorem ordinary_product {n m : ℕ} (a : GammaOrdinaryCharts.Chart B m) (b : GammaOrdinaryCharts.Chart B n) :
    ordinaryClass (nativeOrdinary hc (GammaOrdinaryCharts.product a b)) =
      ordinaryClass (nativeOrdinary hc a) * ordinaryClass (nativeOrdinary hc b) := by
  rw [← ordinary_iso (ordinaryProductHom a b)]
  change (ofRingHom : GammaGroundGammaPositiveSemiring hc B →+* GammaGroundGammaGrothendieckRing hc B)
    (gammaGroundGammaSemiringClass ((nativeOrdinary hc b).product (nativeOrdinary hc a))) = _
  rw [gammaGroundGammaSemiringClass_product, map_mul]
  exact mul_comm (ordinaryClass (nativeOrdinary hc b)) (ordinaryClass (nativeOrdinary hc a))

def measuredProductHom {n m : ℕ} (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    GammaGroundMeasuredGammaHom ((nativeMeasured hc b).product (nativeMeasured hc a))
      (nativeMeasured hc (GammaChartOperations.product a b)) where
  underlying := ordinaryProductHom (GammaOrdinaryCharts.ofWeighted a) (GammaOrdinaryCharts.ofWeighted b)
  preserves u := by
    let G := native hc b.support b.support_definable
    let H := native hc a.support a.support_definable
    change (i : Fin (1 * 1)) × (gammaGroundGammaAppendMap G H).image at u
    rcases u with ⟨i, z⟩
    obtain ⟨p, hp⟩ := z.property
    let x : G := ⟨p.val.1, p.property.1⟩
    let y : H := ⟨p.val.2, p.property.2⟩
    have he : (gammaGroundGammaAppendBijection G H).map p = z := Subtype.ext hp
    subst z
    have hw := gammaGroundMeasuredGammaProduct_combined (nativeMeasured hc b) (nativeMeasured hc a) i x y
    change ((nativeMeasured hc b).product (nativeMeasured hc a)).combinedWeight
      ⟨i, (gammaGroundGammaAppendBijection G H).map p⟩ = _ at hw
    rw [hw, nativeMeasured_weight, nativeMeasured_weight, nativeMeasured_weight]
    change b.volume x.val * (∏ i, cast (gammaCarrier hc) (x.val i)) *
      (a.volume y.val * ∏ i, cast (gammaCarrier hc) (y.val i)) =
      (GammaChartOperations.product a b).volume
        (Fin.append x.val y.val ∘ Section3RVProductBridge.productIndices n m) *
        ∏ i, cast (gammaCarrier hc) ((Fin.append x.val y.val ∘ Section3RVProductBridge.productIndices n m) i)
    rw [Section3GammaProductBridge.append_permute,
      GammaChartOperations.product_volume_join a b y.val y.property x.val x.property]
    have hprod := (Section3GammaProductBridge.permutation n m).prod_comp
      (fun i => cast (gammaCarrier hc) (Fin.append x.val y.val i))
    change (∏ i, cast (gammaCarrier hc) ((Fin.append x.val y.val ∘ Section3RVProductBridge.productIndices n m) i)) = _ at hprod
    rw [Section3GammaProductBridge.append_permute] at hprod
    rw [hprod, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ac_rfl

theorem measured_product {n m : ℕ} (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    measuredClass (nativeMeasured hc (GammaChartOperations.product a b)) =
      measuredClass (nativeMeasured hc a) * measuredClass (nativeMeasured hc b) := by
  rw [← measured_iso (measuredProductHom a b)]
  change (ofRingHom : GammaGroundMeasuredGammaPositiveSemiring hc B →+* GammaGroundMeasuredGammaGrothendieckRing hc B)
    (gammaGroundMeasuredGammaSemiringClass ((nativeMeasured hc b).product (nativeMeasured hc a))) = _
  rw [gammaGroundMeasuredGammaSemiringClass_product, map_mul]
  exact mul_comm (measuredClass (nativeMeasured hc b)) (measuredClass (nativeMeasured hc a))

end DiamondIntegral.Section4.Section3GammaBasicClasses
