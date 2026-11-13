import «section 4».Section3RVChartBridge
import «section 4».Section3RVFormBridge
import «section 4».RVMeasuredIsomorphisms

/-! Measured RV conversions preserve the actual combined weight. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3MeasuredRVChartBridge
open RVMeasuredCharts Section3RVCodeBridge Section3RVFormBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem codeValue_finite (t : Section2.RV M) : codeValue t.val.val = Section2.rvFiniteValue t := by
  have ht : NonzeroRV t.val.val := ⟨t.val.property, fun h => t.property (Subtype.ext h)⟩
  rw [codeValue, dif_pos ht]
  rfl

def chart {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) : Chart B k :=
  { Section3RVChartBridge.chart U.underlying with
    volume := rawForm U.form
    volume_definable := rawForm_definable U.form }

def native (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : Chart B k) :
    GammaGroundMeasuredRVObject hc B k :=
  ⟨Section3RVChartBridge.native hc a, ofRawForm a.domain a.domain_definable a.volume a.volume_definable⟩

def chartRES {k : ℕ} (X : GammaGroundMeasuredRESObject hc B k) : RESChart B k :=
  ⟨chart X.obj, (Section3RVChartBridge.chartRES (⟨X.obj.underlying, X.property⟩ : GammaGroundRESObject hc B k)).finite_values⟩

def nativeRES (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : RESChart B k) :
    GammaGroundMeasuredRESObject hc B k :=
  ⟨native hc a.toChart, (Section3RVChartBridge.nativeRES hc a).property⟩

theorem chart_weight {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) (a : U.underlying.domain) :
    (chart U).correctedWeight (rvValues a.val) = U.combinedWeight a := by
  change rawForm U.form (rvValues a.val) *
      ∏ i, codeValue (rawMap U.underlying.volume (rvValues a.val) i) =
    gammaGroundFormValue U.form a * ∏ i, Section2.rvFiniteValue (U.underlying.target a i)
  rw [rawForm_apply, rawMap_apply]
  simp only [gammaGroundFormValue, gammaCarrier, cast_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact codeValue_finite (U.underlying.target a i)

theorem native_weight {k : ℕ} (a : Chart B k) (u : (native hc a).underlying.domain) :
    (native hc a).combinedWeight u = a.correctedWeight (rvValues u.val) := by
  change a.volume (rvValues u.val) *
      ∏ i, Section2.rvFiniteValue ((Section3RVChartBridge.native hc a).target u i) =
    a.volume (rvValues u.val) * ∏ i, codeValue (a.coordinate (rvValues u.val) i)
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (codeValue_finite ((Section3RVChartBridge.native hc a).target u i)).symm

def chartIso {k : ℕ} {U V : GammaGroundMeasuredRVObject hc B k}
    (f : GammaGroundMeasuredRVHom U V) : Iso (chart U) (chart V) where
  equiv := (RVForgetScissors.ofMap (chart U) (chart V) (rawMap f.bijection.map)
    (rawMap_definable f.bijection.map) (rawMap_bijective f.bijection.map f.bijection.bijective)).equiv
  graph_definable := (RVForgetScissors.ofMap (chart U) (chart V) (rawMap f.bijection.map)
    (rawMap_definable f.bijection.map) (rawMap_bijective f.bijection.map f.bijection.bijective)).graph_definable
  weight_eq u := by
    let a := (rawEquiv U.underlying.domain).symm u
    have ha : rvValues a.val = u.val := rawEquiv_symm_value U.underlying.domain u
    change (chart U).correctedWeight u.val = (chart V).correctedWeight (rawMap f.bijection.map u.val)
    rw [← ha, rawMap_apply]
    exact (chart_weight U a).trans ((f.preserves a).trans (chart_weight V (f.bijection.map a)).symm)

end DiamondIntegral.Section4.Section3MeasuredRVChartBridge
