import «section 4».Section3GammaNativeIsomorphisms
import «section 4».GammaRVIdentityIso
import «section 3».MeasuredGammaPieceWeights

/-! Single Gamma chart conversions are inverse on supports and preserve
the partial form on every point of that support. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaRoundtripBridge
open Section3GammaChartBridge Section3GammaCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem ordinary_chart_native {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    chart (native hc a.support a.support_definable) = a := by cases a; rfl

theorem ordinary_native_chart {n : ℕ} (G : GammaGroundGammaPiece hc B n) :
    nativeOrdinary hc (chart G) = GammaGroundGammaObject.single G := rfl

def measured_chart_native {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    GammaRVChartPresentation.RVVolumeIso
      (measuredChart (native hc a.support a.support_definable)
        (form hc a.support a.support_definable a.normalizedVolume a.normalizedVolume_definable)) a :=
  GammaRVIdentityIso.sameDomainIso _ _ rfl (fun γ hγ =>
    (measuredChart_volume _ _ ⟨γ, hγ⟩).trans (a.normalizedVolume_on γ hγ))

def measured_native_chart {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    GammaGroundMeasuredGammaHom (nativeMeasured hc (measuredChart G w)) (gammaGroundMeasuredGammaSingleForm G w) where
  underlying := GammaGroundGammaHom.id (GammaGroundGammaObject.single G)
  preserves u := by
    rw [nativeMeasured_weight]
    exact congrArg (fun γ => γ * ∏ i, cast (gammaCarrier hc) (u.2.val i)) (measuredChart_volume G w u.2)

end DiamondIntegral.Section4.Section3GammaRoundtripBridge
