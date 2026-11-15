import «section 5».NativePrincipalChartBridge
import «section 5».NativeGeometricPadding
import «section 3».GammaGroundCitedUnmeasuredIntegral

/-! The actual native VF integral and its bounded and geometric values.
Only the precise accepted Section 3 lifting/kernel input is retained;
the original-ground principal-to-chart bridge is proved here. -/
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

def nativeRVChartNormalized (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundRVGrothendieckRing hc B →+* RVOrdinaryPNormalization.Ring B :=
  (RVOrdinaryPNormalization.quotient B).comp (Section3RVChartRingMaps.ordinary hc B)

theorem nativeRVChartNormalized_principal :
    nativeRVChartNormalized hc B (gammaGroundRVPrincipalElement hc B) = 1 := by
  change RVOrdinaryPNormalization.quotient B
    (Section3RVChartRingMaps.ordinary hc B (gammaGroundRVPrincipalElement hc B)) = 1
  rw [nativePrincipal_chart_class,RVOrdinaryPNormalization.p_one]

def nativeRVPositiveNormalized : (gammaGroundRVSpecialCongruence hc B).Quotient →+*
    RVOrdinaryPNormalization.Ring B :=
  (gammaGroundRVSpecialCongruence hc B).lift ((nativeRVChartNormalized hc B).comp ofRingHom) (by
    apply RingCon.ringConGen_le.mpr
    rintro a b ⟨rfl,rfl⟩
    have he := nativeRVChartNormalized_principal (hc := hc) (B := B)
    change nativeRVChartNormalized hc B
      (ordinaryClass (GammaGroundRVObject.ofReal (rvOneObject B.real)) -
        ordinaryClass (GammaGroundRVObject.ofReal (rvPositiveObject hc B.real))) = 1 at he
    rw [map_sub] at he
    change nativeRVChartNormalized hc B (of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvOneObject B.real)))) =
      nativeRVChartNormalized hc B (of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (rvPositiveObject hc B.real)) + 1))
    rw [map_add,←one_def,map_add,map_one]
    change _ = _ + 1
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _))

variable {C : GammaGroundContext M}

def nativeVFChartIntegralPositive (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFPositiveSemiring hc C.base →+* RVOrdinaryPNormalization.Ring C.base :=
  (nativeRVPositiveNormalized (hc := hc) (B := C.base)).comp
    (gammaGroundUnmeasuredPositiveIntegral H).toRingHom

def nativeVFChartIntegral (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFGrothendieckRing hc C.base →+* RVOrdinaryPNormalization.Ring C.base :=
  liftRingHom (nativeVFChartIntegralPositive H)

theorem nativeVFChartIntegral_lift_class (H : YinGammaGroundUnmeasuredLiftInput C hc)
    {k : ℕ} (U : GammaGroundRVObject hc C.base k) :
    nativeVFChartIntegral H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      RVOrdinaryPNormalization.quotient C.base
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) := by
  rw [nativeVFChartIntegral,liftRingHom_apply_of]
  change nativeRVPositiveNormalized (gammaGroundUnmeasuredPositiveIntegral H
    (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) = _
  rw [gammaGroundUnmeasuredPositiveIntegral_lift_class]
  change (gammaGroundRVSpecialCongruence hc C.base).lift
    ((nativeRVChartNormalized hc C.base).comp ofRingHom) _
    ((gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVSemiringClass U)) = _
  rw [RingCon.lift_mk']
  change RVOrdinaryPNormalization.quotient C.base
    (Section3RVChartRingMaps.ordinary hc C.base (ordinaryClass U)) = _
  rw [Section3RVChartRingMaps.ordinary_class]

variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))

def nativeVFBoundedValue (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFGrothendieckRing hc C.base →+* RESDimensionFreeReduction.Ring C.base :=
  (RVT001OrdinaryNormalization.bounded C.model00 linear C.uncountable.le C.saturated C.base
    C.small_real C.small_gamma C.nontrivial_definable_gamma
    (Section3T001Integration.ordinary (hc := hc) C.uncountable.le C.saturated C.model00
      C.small_real C.small_gamma C.nontrivial_definable_gamma)).comp (nativeVFChartIntegral H)

def nativeVFGeometricValue (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    GammaGroundVFGrothendieckRing hc C.base →+* RESAffineLocalization.Target C.base :=
  (nativeGeometricRetraction C.model00 linear C.uncountable.le C.saturated hc C.base
    C.small_real C.small_gamma C.nontrivial_definable_gamma).comp (nativeVFChartIntegral H)

theorem nativeVFBoundedValue_lift_class (H : YinGammaGroundUnmeasuredLiftInput C hc)
    {k : ℕ} (U : GammaGroundRVObject hc C.base k) :
    nativeVFBoundedValue linear H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      nativeGroundRVEvaluation C.model00 linear C.uncountable.le C.saturated hc C.base
        C.small_real C.small_gamma C.nontrivial_definable_gamma .bounded (ordinaryClass U) := by
  change RVT001OrdinaryNormalization.bounded _ _ _ _ _ _ _ _ _ (nativeVFChartIntegral H _) = _
  rw [nativeVFChartIntegral_lift_class,nativeGroundRVEvaluation_class]
  rfl

theorem nativeVFGeometricValue_lift_class (H : YinGammaGroundUnmeasuredLiftInput C hc)
    {k : ℕ} (U : GammaGroundRVObject hc C.base k) :
    nativeVFGeometricValue linear H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))) =
      nativeGroundGeometricRetraction C.model00 linear C.uncountable.le C.saturated
        C.small_real C.small_gamma C.nontrivial_definable_gamma (ordinaryClass U) := by
  unfold nativeVFGeometricValue nativeGroundGeometricRetraction
  rw [RingHom.comp_apply,nativeVFChartIntegral_lift_class,RingHom.comp_apply,
    RingHom.comp_apply,Section3RVChartRingMaps.ordinary_class]

end DiamondIntegral.Section5
