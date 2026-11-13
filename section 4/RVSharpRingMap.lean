import «section 4».RVSharpProducts
import «section 4».RVSharpScissors
import «section 4».RVGrading

/-! The full-proper-preimage map descends from the Gamma presentation with
actual RV-contraction lifts to the actual measured RV chart ring. No
all-bijections Gamma quotient or tensor isomorphism is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVSharpRingMap
open RVSharpCharts RVSharpProducts RVSharpScissors
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def freeMap (B : Base (M := M)) :
    FreeCommRing (GammaChartPresentation.Generator B) →+* RVChartRing.Ring B :=
  FreeCommRing.lift (fun a => RVChartRing.objectClass (sharpChart a.2))

theorem freeMap_symbol (B : Base (M := M)) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    freeMap B (GammaChartPresentation.symbol a) = RVChartRing.objectClass (sharpChart a) :=
  FreeCommRing.lift_of _ _

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (GammaChartPresentation.Generator B))
    (hr : GammaRVChartPresentation.Relation B r) : freeMap B r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, sharp_unit_class, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, sharp_product_class, sub_self]
  | iso a b F =>
    rw [map_sub, freeMap_symbol, freeMap_symbol, RVChartRing.objectClass_iso (sharpIso F), sub_self]
  | empty n μ hμ => rw [freeMap_symbol, RVChartRing.objectClass_empty _ (sharp_empty B n μ hμ)]
  | scissor n I J hI hJ hU hN μ hμ =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (RVChartRing.objectClass_scissor _ _ _ _ (sharp_scissor B n I J hI hJ hU hN μ hμ))

theorem ideal_zero (B : Base (M := M)) :
    GammaRVChartPresentation.relationIdeal B ≤ RingHom.ker (freeMap B) := by
  apply Ideal.span_le.mpr
  intro r hr
  exact relation_zero B r hr

def sharp (B : Base (M := M)) : GammaRVChartPresentation.ChartRing B →+* RVChartRing.Ring B :=
  Ideal.Quotient.lift (GammaRVChartPresentation.relationIdeal B) (freeMap B) (fun _ hr => ideal_zero B hr)

theorem sharp_class (B : Base (M := M)) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    sharp B (Ideal.Quotient.mk (GammaRVChartPresentation.relationIdeal B) (GammaChartPresentation.symbol a)) =
      RVChartRing.objectClass (sharpChart a) := freeMap_symbol B a

theorem sharp_class_mem (B : Base (M := M)) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    sharp B (Ideal.Quotient.mk (GammaRVChartPresentation.relationIdeal B) (GammaChartPresentation.symbol a)) ∈
      RVGrading.gradedPiece B n := by
  rw [sharp_class]
  exact RVGrading.class_mem B _

end DiamondIntegral.Section4.RVSharpRingMap
