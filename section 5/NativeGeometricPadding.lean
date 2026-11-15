import «section 5».NativeGeometricRetraction
import «section 5».NativeRVObjectEvaluation
import «section 3».GammaGroundRVCoproducts
import «section 4».Section3RVRoundtripBridge

/-! Actual positive RV affine-line padding realizes denominator clearing
for the native geometric retraction. Its raw value is the affine class;
its normalized value is one, without a cancellation hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeAffineRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundRVObject hc B 1 :=
  (Section3RVChartBridge.native hc (RESFibreObjects.torus B).toChart).coprod
    (Section3RVChartBridge.native hc (RESFibreObjects.point B).toChart)

def nativeAffineRVPower (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    (r : ℕ) → GammaGroundRVObject hc B r
  | 0 => GammaGroundRVObject.unit hc B
  | r+1 => (nativeAffineRVPower hc B r).product (nativeAffineRVObject hc B)

theorem nativeOrdinaryClass_coprod {k : ℕ} (U V : GammaGroundRVObject hc B k) :
    ordinaryClass (U.coprod V) = ordinaryClass U + ordinaryClass V := by
  have he := congrArg (gammaGroundRVKPlusToSemiring (M := M) (hc := hc) (ground := B))
    (gammaGroundRVClass_coprod U V)
  simp only [map_add,gammaGroundRVKPlusToSemiring_class] at he
  exact (congrArg (of : GammaGroundRVPositiveSemiring hc B → GammaGroundRVGrothendieckRing hc B) he).trans (map_add _ _ _)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem nativeGroundRVEvaluation_native_chart (kind : EulerKind) {k : ℕ} (a : RVMeasuredCharts.Chart B k) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (ordinaryClass (Section3RVChartBridge.native hc a)) =
      nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass a) := by
  rw [nativeGroundRVEvaluation_class,RVOrdinaryRing.objectClass_iso (Section3RVRoundtripBridge.chart_native a)]

theorem nativeAffineRVObject_raw_value (kind : EulerKind) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (ordinaryClass (nativeAffineRVObject hc B)) = RESAffineLocalization.dimensionFreeAffine B := by
  unfold nativeAffineRVObject
  rw [nativeOrdinaryClass_coprod,map_add,nativeGroundRVEvaluation_native_chart,
    nativeGroundRVEvaluation_native_chart]
  have hres (a : RVMeasuredCharts.RESChart B 1) :
      nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass a.toChart) =
        RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass a) := by
    rw [←RVOrdinaryMaps.ofRES_class,nativeRVEvaluation_res]
  rw [hres,hres]
  exact (map_add (RESDimensionFreeReduction.fromGradedReduced B)
    (RESOrdinaryReduction.torusClass B) (RESOrdinaryReduction.pointClass B)).symm

theorem nativeAffineRVPower_raw_value (kind : EulerKind) (r : ℕ) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (ordinaryClass (nativeAffineRVPower hc B r)) = RESAffineLocalization.dimensionFreeAffine B ^ r := by
  induction r with
  | zero =>
    change nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (of (gammaGroundRVSemiringClass (GammaGroundRVObject.unit hc B))) = _
    rw [gammaGroundRVSemiringClass_unit,←one_def,map_one,pow_zero]
  | succ r ih =>
    change nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (ordinaryClass ((nativeAffineRVPower hc B r).product (nativeAffineRVObject hc B))) = _
    rw [nativeGroundRVEvaluation_product,ih,nativeAffineRVObject_raw_value,pow_succ]

def nativeGroundGeometricRetraction : GammaGroundRVGrothendieckRing hc B →+* RESAffineLocalization.Target B :=
  (nativeGeometricRetraction h00 linear hκ hs hc B hr hγ hΓ).comp
    ((RVOrdinaryPNormalization.quotient B).comp (Section3RVChartRingMaps.ordinary hc B))

theorem nativeGroundGeometricRetraction_class {k : ℕ} (U : GammaGroundRVObject hc B k) :
    nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ (ordinaryClass U) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .geometric (ordinaryClass U)) k := by
  unfold nativeGroundGeometricRetraction
  rw [RingHom.comp_apply,RingHom.comp_apply,Section3RVChartRingMaps.ordinary_class,
    nativeGeometricRetraction_class,nativeGroundRVEvaluation_class]

theorem nativeGroundGeometricRetraction_affine_padding {k : ℕ}
    (U : GammaGroundRVObject hc B k) (r : ℕ) :
    nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ
        (ordinaryClass (U.product (nativeAffineRVPower hc B r))) =
      nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ (ordinaryClass U) := by
  rw [nativeGroundGeometricRetraction_class,nativeGroundRVEvaluation_product,
    nativeAffineRVPower_raw_value,nativeGroundGeometricRetraction_class,mul_comm]
  exact geometricDegreeValue_affine_padding _ _ _ _

theorem nativeGroundGeometricRetraction_eq_iff_common_degree {k l : ℕ}
    (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ (ordinaryClass U) =
      nativeGroundGeometricRetraction h00 linear hκ hs hr hγ hΓ (ordinaryClass V) ↔
      ∃ N : ℕ,k ≤ N ∧ l ≤ N ∧
        nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .geometric
          (ordinaryClass (U.product (nativeAffineRVPower hc B (N-k)))) =
        nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ .geometric
          (ordinaryClass (V.product (nativeAffineRVPower hc B (N-l)))) := by
  simp only [nativeGroundGeometricRetraction_class,geometricDegreeValue_eq_iff,
    nativeGroundRVEvaluation_product,nativeAffineRVPower_raw_value,mul_comm]

end DiamondIntegral.Section5
