import «section 4».Section3RVRoundtripBridge
import «section 4».RVChartRestrictions
import «section 3».GammaGroundMeasuredRVScissors

/-! Actual definable cuts commute with both RV encodings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVRestrictionBridge
open RVMeasuredCharts Section3RVCodeBridge RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem rawDomain_mono {n : ℕ} {D E : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
    (h : D.carrier ⊆ E.carrier) : rawDomain D ⊆ rawDomain E :=
  Set.image_mono h

theorem rawDomain_sdiff {n : ℕ} (D E : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    rawDomain (D.sdiff E) = rawDomain D \ rawDomain E :=
  Set.image_diff rvValues_injective D.carrier E.carrier

def restrictionIso {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    RVForgetScissors.UnderlyingIso (Section3RVChartBridge.chart (U.restrict X hX))
      (restrict (ofChart (Section3RVChartBridge.chart U)) (rawDomain X)
        (rawDomain_definable X) (rawDomain_mono hX)).toChart :=
  RVForgetScissors.ofMap _ _ id (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable X))
    (Set.bijOn_id _)

def measuredRestrictionIso {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    Iso (Section3MeasuredRVChartBridge.chart (U.restrict X hX))
      (restrict (ofChart (Section3MeasuredRVChartBridge.chart U)) (rawDomain X)
        (rawDomain_definable X) (rawDomain_mono hX)).toChart where
  equiv := (restrictionIso U.underlying X hX).equiv
  graph_definable := (restrictionIso U.underlying X hX).graph_definable
  weight_eq u := by
    let a := (rawEquiv X).symm u
    have ha := rawEquiv_symm_value X u
    change (Section3MeasuredRVChartBridge.chart (U.restrict X hX)).correctedWeight u.val =
      (Section3MeasuredRVChartBridge.chart U).correctedWeight u.val
    rw [← ha]
    exact (Section3MeasuredRVChartBridge.chart_weight (U.restrict X hX) a).trans
      (Section3MeasuredRVChartBridge.chart_weight U (GammaGroundMap.inclusion hX a)).symm

def nativeRestrictionIso {k : ℕ} (a : Chart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) (hs : I ⊆ a.domain) :
    GammaGroundBijection
      ((Section3RVChartBridge.native hc a).restrict (ofRaw I hI) (fun _ hx => hs hx)).domain
      (Section3RVChartBridge.native hc (restrict (ofChart a) I hI hs).toChart).domain :=
  GammaGroundBijection.id (ofRaw I hI)

def nativeMeasuredRestrictionIso {k : ℕ} (a : Chart B k) (I : Set (Fin a.arity → M))
    (hI : DefinableOverBase B (fun _ : Fin a.arity => .rv) I) (hs : I ⊆ a.domain) :
    GammaGroundMeasuredRVHom
      ((Section3MeasuredRVChartBridge.native hc a).restrict (ofRaw I hI) (fun _ hx => hs hx))
      (Section3MeasuredRVChartBridge.native hc (restrict (ofChart a) I hI hs).toChart) where
  bijection := nativeRestrictionIso a I hI hs
  preserves _ := rfl

end DiamondIntegral.Section4.Section3RVRestrictionBridge
