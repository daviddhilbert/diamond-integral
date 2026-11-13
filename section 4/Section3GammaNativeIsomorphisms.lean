import «section 4».Section3GammaNativeCodeMaps
import «section 3».GammaGroundFamilyPieceMaps

/-! Chart Gamma isomorphisms give actual native contracted arrows.
Measured arrows retain the original form and combined weight. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaNativeIsomorphisms
open Section3GammaChartBridge Section3GammaCodeBridge Section3GammaNativeCodeMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinary {n : ℕ} {a b : GammaOrdinaryCharts.Chart B n} (f : GammaOrdinaryCharts.Iso a b) :
    GammaGroundGammaHom (nativeOrdinary hc a) (nativeOrdinary hc b) where
  bijection := GammaGroundFamilyBijection.pieces (nativeOrdinary hc a) _ (fun _ => gammaBijection f)
  contraction := ⟨GammaGroundFamilyBijection.pieces (nativeOrdinary hc a).codeLift _ (fun _ => codeBijection f), by
    intro c
    change (⟨c.1, (gammaGroundCodeDecode (native hc b.support b.support_definable)) ((codeBijection f).map c.2)⟩ :
        (nativeOrdinary hc b).Carrier) =
      ⟨c.1, (gammaBijection f).map (gammaGroundCodeDecode (native hc a.support a.support_definable) c.2)⟩
    exact congrArg (Sigma.mk c.1) (Subtype.ext (codeBijection_quotient f c.2))⟩

def measured {n : ℕ} {a b : GammaWeightedCharts.Chart B n} (f : GammaRVChartPresentation.RVVolumeIso a b) :
    GammaGroundMeasuredGammaHom (nativeMeasured hc a) (nativeMeasured hc b) where
  underlying := ordinary (GammaOrdinaryCharts.ofMeasured f)
  preserves u := by
    rw [nativeMeasured_weight, nativeMeasured_weight]
    change a.volume u.2.val * (∏ i, cast (gammaCarrier hc) (u.2.val i)) =
      b.volume (f.map u.2.val) * ∏ i, f.map u.2.val i
    have h := (eq_div_iff_mul_eq').mp (f.volume_eq u.2.val u.2.property)
    simpa only [gammaCarrier, cast_eq] using h

end DiamondIntegral.Section4.Section3GammaNativeIsomorphisms
