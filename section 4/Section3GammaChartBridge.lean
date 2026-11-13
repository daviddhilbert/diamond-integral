import «section 4».Section3GammaCodeBridge
import «section 4».GammaOrdinaryCharts
import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundGammaVolumeCategories

/-! Actual Gamma pieces and partial volume forms in both encodings.
Totalization is by one outside the domain and adds no ground parameters. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaChartBridge
open GammaOrderLogic GammaDefinableMaps Section3GammaCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def chart {n : ℕ} (G : GammaGroundGammaPiece hc B n) : GammaOrdinaryCharts.Chart B n :=
  ⟨G.carrier, (native_iff G.carrier).mp G.definable⟩

def nativeOrdinary (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    GammaGroundGammaObject hc B n :=
  GammaGroundGammaObject.single (native hc a.support a.support_definable)

def totalForm {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
  Classical.choose (gammaGroundGammaForm_total_function G w)

theorem totalForm_definable {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    MapDefinable B (totalForm G w) :=
  (function_iff _).mp (Classical.choose_spec (gammaGroundGammaForm_total_function G w)).1

theorem totalForm_on {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) (a : G) :
    totalForm G w a.val = gammaGroundFormValue w a :=
  (Classical.choose_spec (gammaGroundGammaForm_total_function G w)).2 a

def measuredChart {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G) :
    GammaWeightedCharts.Chart B n :=
  GammaChartOperations.ofTotal B n G.carrier ((native_iff G.carrier).mp G.definable)
    (totalForm G w) (totalForm_definable G w)

theorem measuredChart_volume {n : ℕ} (G : GammaGroundGammaPiece hc B n) (w : GammaGroundVolumeForm hc B G)
    (a : G) : (measuredChart G w).volume a.val = gammaGroundFormValue w a := totalForm_on G w a

def nativeMeasured (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    GammaGroundMeasuredGammaObject hc B n where
  underlying := nativeOrdinary hc (GammaOrdinaryCharts.ofWeighted a)
  form _ := form hc a.support a.support_definable a.normalizedVolume a.normalizedVolume_definable

theorem nativeMeasured_weight {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (u : (nativeMeasured hc a).underlying.Carrier) :
    (nativeMeasured hc a).combinedWeight u = a.volume u.2.val * ∏ i, cast (gammaCarrier hc) (u.2.val i) := by
  change a.normalizedVolume u.2.val * ∏ i, cast (gammaCarrier hc) (u.2.val i) = _
  rw [a.normalizedVolume_on _ u.2.property]

def ordinaryFamily {n : ℕ} (A : GammaGroundGammaObject hc B n) :
    Fin A.tags → GammaOrdinaryCharts.Chart B n := fun i => chart (A.piece i)

def measuredFamily {n : ℕ} (A : GammaGroundMeasuredGammaObject hc B n) :
    Fin A.underlying.tags → GammaWeightedCharts.Chart B n := fun i => measuredChart (A.underlying.piece i) (A.form i)

theorem measuredFamily_weight {n : ℕ} (A : GammaGroundMeasuredGammaObject hc B n) (u : A.underlying.Carrier) :
    (measuredFamily A u.1).volume u.2.val * (∏ i, cast (gammaCarrier hc) (u.2.val i)) = A.combinedWeight u := by
  exact congrArg (fun γ => γ * ∏ i, cast (gammaCarrier hc) (u.2.val i))
    (measuredChart_volume (A.underlying.piece u.1) (A.form u.1) u.2)

end DiamondIntegral.Section4.Section3GammaChartBridge
