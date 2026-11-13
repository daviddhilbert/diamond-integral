import «section 4».RVCoefficientShearGraphs
import «section 4».RVUnaryScaling
import «section 4».RVMeasuredProductProperties

/-! A retained RV coefficient coordinate of constant value supplies an
actual measured isomorphism translating a unary Gamma factor. No
original-base RV point of that value is assumed or selected. The target
Gamma volume is compensated, so the full corrected weight is preserved. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientTranslation
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVRealProducts
open FiniteTupleBlocks GammaRVChartPresentation GammaTranslation RVNamedMultiplication
open RVCoefficientShearGraphs RVUnaryScaling
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def coefficientCode {a : ℕ} (j : Fin a) (x : Fin a → M) (hx : NonzeroRV (x j)) : Code (M := M) :=
  ⟨⟨x j, hx.1⟩, hx.2⟩

theorem coefficientCode_value {a : ℕ} (j : Fin a) (x : Fin a → M) (hx : NonzeroRV (x j)) :
    value (coefficientCode j x hx) = codeValue (x j) := (codeValue_raw _).symm

def translatedChart (B : Base (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (c : GammaWeightedCharts.Chart B 1) : GammaWeightedCharts.Chart B 1 :=
  GammaTranslationCharts.translatedChart B (fun _ : Fin 1 => δ) (fun _ => hδ) c

theorem shear_bijective (B : Base (M := M)) {k : ℕ} (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaWeightedCharts.Chart B 1) :
    Set.BijOn (shear j) (product r (RVSharpCharts.sharpChart c)).domain
      (product r (RVSharpCharts.sharpChart (translatedChart B δ hδ c))).domain := by
  change Set.BijOn (shear j) (productSet r.domain (sharp c.support))
    (productSet r.domain (sharp (translatedChart B δ hδ c).support))
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx, z, hz, rfl⟩ := (productSet_exists r.domain (sharp c.support) u).mp hu
    rw [shear_join, productSet_join]
    refine ⟨hx, ?_⟩
    let t := coefficientCode j x (hp x hx)
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    have h := (scale_sharp_bijective t c.support).mapsTo hz
    rw [ht] at h
    exact h
  · intro u hu v hv' he
    obtain ⟨x, hx, z, hz, rfl⟩ := (productSet_exists r.domain (sharp c.support) u).mp hu
    obtain ⟨y, hy, w, hw, rfl⟩ := (productSet_exists r.domain (sharp c.support) v).mp hv'
    rw [shear_join, shear_join] at he
    have hxy : x = y := by
      funext i
      have h := congrFun he (headIndex 1 r.arity i)
      simpa only [join_head] using h
    subst y
    have hzw : z = w := by
      let t := coefficientCode j x (hp x hx)
      apply RVScaledRays.scale_injective t (hz.1 0) (hw.1 0)
      funext i
      change scale (x j) z i = scale (x j) w i
      have h := congrFun he (tailIndex 1 r.arity i)
      simpa only [join_tail] using h
    rw [hzw]
  · intro u hu
    obtain ⟨x, hx, z, hz, rfl⟩ :=
      (productSet_exists r.domain (sharp (translatedChart B δ hδ c).support) u).mp hu
    let t := coefficientCode j x (hp x hx)
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    have hb := scale_sharp_bijective t c.support
    rw [ht] at hb
    obtain ⟨w, hw, he⟩ := hb.surjOn hz
    refine ⟨join 1 r.arity x w, (productSet_join r.domain (sharp c.support) x w).mpr ⟨hx, hw⟩, ?_⟩
    rw [shear_join]
    exact congrArg (join 1 r.arity x) he

def iso (B : Base (M := M)) {k : ℕ} (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaWeightedCharts.Chart B 1) :
    Iso (product r (RVSharpCharts.sharpChart c))
      (product r (RVSharpCharts.sharpChart (translatedChart B δ hδ c))) where
  equiv := Set.BijOn.equiv (shear j) (shear_bijective B r j hp δ hv hδ c)
  graph_definable := (RVForgetScissors.ofMap (product r (RVSharpCharts.sharpChart c))
    (product r (RVSharpCharts.sharpChart (translatedChart B δ hδ c))) (shear j)
    (RVCoefficientShearGraphs.graph_definable B _ (product r (RVSharpCharts.sharpChart c)).domain_definable j)
    (shear_bijective B r j hp δ hv hδ c)).graph_definable
  weight_eq := by
    intro u
    change (product r (RVSharpCharts.sharpChart c)).correctedWeight u.val =
      (product r (RVSharpCharts.sharpChart (translatedChart B δ hδ c))).correctedWeight (shear j u.val)
    obtain ⟨x, hx, z, hz, he⟩ := (productSet_exists r.domain (sharp c.support) u.val).mp u.property
    rw [he, shear_join]
    let t := coefficientCode j x (hp x hx)
    have ht : value t = δ := (coefficientCode_value j x (hp x hx)).trans (hv x hx)
    exact (product_weight_join r (RVSharpCharts.sharpChart c) x z).trans
      ((congrArg (r.correctedWeight x * ·) (scale_weight B δ hδ c t ht z hz)).trans
        (product_weight_join r (RVSharpCharts.sharpChart (translatedChart B δ hδ c)) x (scale (x j) z)).symm)

end DiamondIntegral.Section4.RVCoefficientTranslation
