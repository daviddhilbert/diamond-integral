import «section 4».Section3GammaRingEquivalences
import «section 4».GammaOrdinaryFiniteSupportFamilies
import «section 4».GammaRestrictedRVFiniteFamilies
import «section 3».GammaGroundFiniteGammaSemiringInclusion
import «section 3».GammaGroundMeasuredFiniteGammaSemiringInclusion

/-! The finite Gamma conversions retain the original base, all family
tags and arbitrary partial volume forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3FiniteGammaChartBridge
open Section3GammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeOrdinary (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ} (a : GammaOrdinaryCharts.FiniteChart B n) :
    GammaGroundFiniteGammaObject hc B n := ⟨Section3GammaChartBridge.nativeOrdinary hc a.toChart, fun _ => a.finite_support⟩
def nativeMeasured (hc : CanonicalStructure.IsCanonical (M := M)) {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) :
    GammaGroundMeasuredFiniteGammaObject hc B n := ⟨Section3GammaChartBridge.nativeMeasured hc a.toChart, fun _ => a.finite_support⟩

def ordinaryFamily {n : ℕ} (A : GammaGroundFiniteGammaObject hc B n) :
    Fin A.obj.tags → GammaOrdinaryCharts.FiniteChart B n := fun i => ⟨chart (A.obj.piece i), A.property i⟩
def measuredFamily {n : ℕ} (A : GammaGroundMeasuredFiniteGammaObject hc B n) :
    Fin A.obj.underlying.tags → GammaFiniteRVCharts.FiniteChart B n :=
  fun i => ⟨measuredChart (A.obj.underlying.piece i) (A.obj.form i), A.property i⟩

def ordinaryValue {n : ℕ} (A : GammaGroundFiniteGammaObject hc B n) : GammaOrdinaryFiniteRing.Ring B :=
  GammaOrdinaryFiniteSupportFamilies.familyClass (ordinaryFamily A)
def measuredValue {n : ℕ} (A : GammaGroundMeasuredFiniteGammaObject hc B n) : GammaFiniteRVPresentation.ChartRing B :=
  GammaRestrictedRVFiniteFamilies.Finite.familyClass (measuredFamily A)

theorem ordinary_value_iso {n : ℕ} {A D : GammaGroundFiniteGammaObject hc B n} (f : GammaGroundGammaHom A.obj D.obj) :
    ordinaryValue A = ordinaryValue D :=
  GammaOrdinaryFiniteSupportFamilies.familyClass_iso (Section3GammaFamilyIsomorphismBridge.ordinary f)
theorem measured_value_iso {n : ℕ} {A D : GammaGroundMeasuredFiniteGammaObject hc B n} (f : GammaGroundMeasuredGammaHom A.obj D.obj) :
    measuredValue A = measuredValue D :=
  GammaRestrictedRVFiniteFamilies.Finite.familyClass_iso (Section3GammaFamilyIsomorphismBridge.measured f)

def ordinaryClass {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n) : GammaGroundFiniteGammaGrothendieckRing hc B :=
  of (gammaGroundFiniteGammaSemiringClass U)
def measuredClass {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n) : GammaGroundMeasuredFiniteGammaGrothendieckRing hc B :=
  of (gammaGroundMeasuredFiniteGammaSemiringClass U)

theorem ordinary_iso {n : ℕ} {U V : GammaGroundFiniteGammaObject hc B n} (f : GammaGroundGammaHom U.obj V.obj) : ordinaryClass U = ordinaryClass V :=
  congrArg of (gammaGroundFiniteGammaSemiringClass_iso ((gammaGroundFiniteGammaProperty (hc := hc) (ground := B) (k := n)).isoMk
    (asIso (show U.obj ⟶ V.obj from f))))
theorem measured_iso {n : ℕ} {U V : GammaGroundMeasuredFiniteGammaObject hc B n} (f : GammaGroundMeasuredGammaHom U.obj V.obj) : measuredClass U = measuredClass V :=
  congrArg of (gammaGroundMeasuredFiniteGammaSemiringClass_iso ((gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := B) (k := n)).isoMk
    (asIso (show U.obj ⟶ V.obj from f))))

end DiamondIntegral.Section4.Section3FiniteGammaChartBridge
