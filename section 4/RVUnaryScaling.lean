import «section 4».RVScaledRays
import «section 4».GammaTranslationCharts

/-! Pointwise RV scaling over arbitrary unary Gamma domains. These are
set-theoretic bijections and corrected-weight identities for an actual
RV multiplier. They make no claim that this multiplier is definable over
the base; a retained coefficient coordinate may provide it instead. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVUnaryScaling
open GammaRVChartPresentation GammaTranslation RVScaledRays RVNamedMultiplication
open GammaRVLifts GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem scale_proper (t : Code (M := M)) (z : Fin 1 → M) (hz : Proper z) :
    Proper (scale (raw t) z) := by
  intro i
  fin_cases i
  exact scale_nonzero t (hz 0)

theorem scale_contraction (t : Code (M := M)) (z : Fin 1 → M) (hz : Proper z) :
    codeValues (scale (raw t) z) = shift (fun _ : Fin 1 => value t) (codeValues z) := by
  funext i
  fin_cases i
  change codeValue (iRVMul (raw t) (z 0)) = value t * codeValue (z 0)
  rw [GammaGroupNames.codeValue_mul _ _ ⟨raw_rv t, raw_ne_zero t⟩ (hz 0), codeValue_raw]

theorem scale_sharp_bijective (t : Code (M := M)) (I : Set (Fin 1 → Values.Gamma (M := M))) :
    Set.BijOn (scale (raw t)) (sharp I) (sharp (translated (fun _ : Fin 1 => value t) I)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ⟨scale_proper t z hz.1, ⟨codeValues z, hz.2, (scale_contraction t z hz.1).symm⟩⟩
  · apply (scale_injective t).mono
    intro z hz
    exact hz.1 0
  · intro z hz
    let u := scale (raw (inverseCode t)) z
    have hu : Proper u := scale_proper (inverseCode t) z hz.1
    have he : scale (raw t) u = z := scale_inverse t z (hz.1 0).1
    obtain ⟨w, hw, hwe⟩ := hz.2
    have hsame : codeValues u = w := by
      have hs : shift (fun _ : Fin 1 => value t) (codeValues u) =
          shift (fun _ : Fin 1 => value t) w := by
        rw [← scale_contraction t u hu, he, hwe]
      exact funext (fun i => mul_left_cancel (congrFun hs i))
    exact ⟨u, ⟨hu, hsame.symm ▸ hw⟩, he⟩

theorem scale_weight (B : Base (M := M)) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (c : GammaWeightedCharts.Chart B 1)
    (t : Code (M := M)) (ht : value t = δ) (z : Fin 1 → M) (hz : z ∈ sharp c.support) :
    (RVSharpCharts.sharpChart c).correctedWeight z =
      (RVSharpCharts.sharpChart (GammaTranslationCharts.translatedChart B
        (fun _ : Fin 1 => δ) (fun _ => hδ) c)).correctedWeight (scale (raw t) z) := by
  have hc := scale_contraction t z hz.1
  rw [ht] at hc
  have hv := (GammaTranslationCharts.translationVolumeIso B
    (fun _ : Fin 1 => δ) (fun _ => hδ) c).volume_eq (codeValues z) hz.2
  change c.volume (codeValues z) * (∏ i, codeValue (z i)) =
    (GammaTranslationCharts.translatedChart B (fun _ : Fin 1 => δ) (fun _ => hδ) c).volume
      (codeValues (scale (raw t) z)) * (∏ i, codeValue (scale (raw t) z i))
  change c.volume (codeValues z) * (∏ i, codeValues z i) =
    (GammaTranslationCharts.translatedChart B (fun _ : Fin 1 => δ) (fun _ => hδ) c).volume
      (codeValues (scale (raw t) z)) * (∏ i, codeValues (scale (raw t) z) i)
  rw [hc]
  exact (eq_div_iff_mul_eq').mp hv

end DiamondIntegral.Section4.RVUnaryScaling
