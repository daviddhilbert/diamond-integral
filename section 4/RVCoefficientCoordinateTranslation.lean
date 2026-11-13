import «section 4».RVCoefficientCoordinateShearGraphs
import «section 4».RVCoefficientTranslation
import «section 4».RVMeasuredProductProperties

/-! A retained RV coefficient coordinate of constant value supplies an
actual measured isomorphism translating one coordinate of an arbitrary Gamma factor. No
original-base RV point of that value is assumed or selected. The target
Gamma volume is compensated, so the full corrected weight is preserved. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientCoordinateTranslation
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVRealProducts
open FiniteTupleBlocks GammaRVChartPresentation GammaTranslation RVNamedMultiplication
open RVCoefficientCoordinateShearGraphs RVCoordinateScaling
open RVCoefficientTranslation (coefficientCode coefficientCode_value)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def translatedChart (B : Base (M := M)) {n : ℕ} (i : Fin n) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (c : GammaWeightedCharts.Chart B n) : GammaWeightedCharts.Chart B n :=
  GammaTranslationCharts.translatedChart B (shiftVector i δ) (shiftVector_definable B i δ hδ) c

theorem shear_bijective (B : Base (M := M)) {k n : ℕ} (r : Chart B k) (j : Fin r.arity) (i : Fin n)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaWeightedCharts.Chart B n) :
    Set.BijOn (shear j i) (product r (RVSharpCharts.sharpChart c)).domain
      (product r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c))).domain := by
  change Set.BijOn (shear j i) (productSet r.domain (sharp c.support))
    (productSet r.domain (sharp (translatedChart B i δ hδ c).support))
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx, z, hz, rfl⟩ := (productSet_exists r.domain (sharp c.support) u).mp hu
    let t := coefficientCode j x (hp x hx)
    rw [shear_join j i x z t rfl, productSet_join]
    refine ⟨hx, ?_⟩
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    have h := (scaleAt_sharp_bijective t i c.support).mapsTo hz
    rw [ht] at h
    exact h
  · intro u hu v hv' he
    obtain ⟨x, hx, z, hz, rfl⟩ := (productSet_exists r.domain (sharp c.support) u).mp hu
    obtain ⟨y, hy, w, hw, rfl⟩ := (productSet_exists r.domain (sharp c.support) v).mp hv'
    let t := coefficientCode j x (hp x hx)
    let s := coefficientCode j y (hp y hy)
    rw [shear_join j i x z t rfl, shear_join j i y w s rfl] at he
    have hxy : x = y := by
      funext i
      have h := congrFun he (headIndex n r.arity i)
      simpa only [join_head] using h
    subst y
    have hzw : z = w := by
      apply scaleAt_injective t i hz.1 hw.1
      funext l
      change scaleAt t i z l = scaleAt t i w l
      have h := congrFun he (tailIndex n r.arity l)
      simpa only [join_tail] using h
    rw [hzw]
  · intro u hu
    obtain ⟨x, hx, z, hz, rfl⟩ :=
      (productSet_exists r.domain (sharp (translatedChart B i δ hδ c).support) u).mp hu
    let t := coefficientCode j x (hp x hx)
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    have hb := scaleAt_sharp_bijective t i c.support
    rw [ht] at hb
    obtain ⟨w, hw, he⟩ := hb.surjOn hz
    refine ⟨join n r.arity x w, (productSet_join r.domain (sharp c.support) x w).mpr ⟨hx, hw⟩, ?_⟩
    rw [shear_join j i x w t rfl]
    exact congrArg (join n r.arity x) he

def iso (B : Base (M := M)) {k n : ℕ} (r : Chart B k) (j : Fin r.arity) (i : Fin n)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaWeightedCharts.Chart B n) :
    Iso (product r (RVSharpCharts.sharpChart c))
      (product r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c))) where
  equiv := Set.BijOn.equiv (shear j i) (shear_bijective B r j i hp δ hv hδ c)
  graph_definable := (RVForgetScissors.ofMap (product r (RVSharpCharts.sharpChart c))
    (product r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c))) (shear j i)
    (RVCoefficientCoordinateShearGraphs.graph_definable B _ (product r (RVSharpCharts.sharpChart c)).domain_definable j i)
    (shear_bijective B r j i hp δ hv hδ c)).graph_definable
  weight_eq := by
    intro u
    change (product r (RVSharpCharts.sharpChart c)).correctedWeight u.val =
      (product r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c))).correctedWeight (shear j i u.val)
    obtain ⟨x, hx, z, hz, he⟩ := (productSet_exists r.domain (sharp c.support) u.val).mp u.property
    let t := coefficientCode j x (hp x hx)
    rw [he]
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    exact (product_weight_join r (RVSharpCharts.sharpChart c) x z).trans
      ((congrArg (r.correctedWeight x * ·) (scaleAt_weight B i δ hδ c t ht z hz)).trans
        ((product_weight_join r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c)) x (scaleAt t i z)).symm.trans
          (congrArg (product r (RVSharpCharts.sharpChart (translatedChart B i δ hδ c))).correctedWeight
            (shear_join j i x z t rfl)).symm))

end DiamondIntegral.Section4.RVCoefficientCoordinateTranslation
