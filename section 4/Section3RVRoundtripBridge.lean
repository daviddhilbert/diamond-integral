import «section 4».Section3MeasuredRVChartBridge

/-! The actual RV conversions are inverse up to original-base definable
isomorphism. In the measured case they preserve the combined weight. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVRoundtripBridge
open RVMeasuredCharts Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def rawRoundtrip {n : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundBijection (ofRaw (rawDomain D) (rawDomain_definable D)) D where
  map := GammaGroundMap.inclusion (by
    intro a ha
    obtain ⟨b, hb, he⟩ := ha
    exact rvValues_injective he ▸ hb)
  bijective := ⟨(by intro a b h; exact Subtype.ext (congrArg (fun x : D => x.val) h)), (by
    intro b
    exact ⟨⟨b.val, b.val, b.property, rfl⟩, rfl⟩)⟩

def nativeIso {k : ℕ} {a b : Chart B k} (F : RVForgetScissors.UnderlyingIso a b) :
    GammaGroundBijection (Section3RVChartBridge.native hc a).domain
      (Section3RVChartBridge.native hc b).domain :=
  let I := RVUnderlyingIsomorphisms.ofFixed F
  bijectionOfRaw a.domain b.domain a.domain_definable b.domain_definable
    I.extension I.extension_graph I.extension_bijOn

def nativeMeasuredIso {k : ℕ} {a b : Chart B k} (F : Iso a b) :
    GammaGroundMeasuredRVHom (Section3MeasuredRVChartBridge.native hc a)
      (Section3MeasuredRVChartBridge.native hc b) where
  bijection := nativeIso (RVForgetScissors.ofMeasured F)
  preserves u := by
    rw [Section3MeasuredRVChartBridge.native_weight, Section3MeasuredRVChartBridge.native_weight]
    let I := RVMeasuredIsomorphisms.underlying F
    change a.correctedWeight (rvValues u.val) = b.correctedWeight (I.extension (rvValues u.val))
    rw [I.extension_on ⟨rvValues u.val, u.property⟩]
    exact F.weight_eq ⟨rvValues u.val, u.property⟩

def native_chart {k : ℕ} (U : GammaGroundRVObject hc B k) :
    GammaGroundBijection (Section3RVChartBridge.native hc (Section3RVChartBridge.chart U)).domain U.domain :=
  rawRoundtrip U.domain

def native_chart_measured {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) :
    GammaGroundMeasuredRVHom
      (Section3MeasuredRVChartBridge.native hc (Section3MeasuredRVChartBridge.chart U)) U where
  bijection := rawRoundtrip U.underlying.domain
  preserves u := by
    rw [Section3MeasuredRVChartBridge.native_weight]
    exact Section3MeasuredRVChartBridge.chart_weight U ((rawRoundtrip U.underlying.domain).map u)

theorem chart_native_domain {k : ℕ} (a : Chart B k) :
    (Section3RVChartBridge.chart (Section3RVChartBridge.native hc a)).domain = a.domain :=
  rawDomain_ofRaw a.domain a.domain_definable

def chart_native {k : ℕ} (a : Chart B k) :
    RVForgetScissors.UnderlyingIso (Section3RVChartBridge.chart (Section3RVChartBridge.native hc a)) a :=
  RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable _)) (by
      rw [chart_native_domain]
      exact Set.bijOn_id a.domain)

theorem chart_native_weight {k : ℕ} (a : Chart B k)
    (x : (Section3MeasuredRVChartBridge.chart (Section3MeasuredRVChartBridge.native hc a)).domain) :
    (Section3MeasuredRVChartBridge.chart (Section3MeasuredRVChartBridge.native hc a)).correctedWeight x.val =
      a.correctedWeight x.val := by
  let u := (rawEquiv (Section3RVChartBridge.native hc a).domain).symm x
  have hu := rawEquiv_symm_value (Section3RVChartBridge.native hc a).domain x
  have h := Section3MeasuredRVChartBridge.chart_weight (Section3MeasuredRVChartBridge.native hc a) u
  rw [Section3MeasuredRVChartBridge.native_weight, hu] at h
  exact h

def chart_native_measured {k : ℕ} (a : Chart B k) :
    Iso (Section3MeasuredRVChartBridge.chart (Section3MeasuredRVChartBridge.native hc a)) a where
  equiv := (chart_native (hc := hc) a).equiv
  graph_definable := (chart_native (hc := hc) a).graph_definable
  weight_eq := chart_native_weight a

end DiamondIntegral.Section4.Section3RVRoundtripBridge
