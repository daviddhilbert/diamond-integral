import «section 4».RVUnaryScaling

/-! Scaling one RV coordinate over arbitrary-dimensional Gamma domains.
The actual multiplier need not be definable over the base. The resulting
set bijection contracts to translation in exactly the chosen coordinate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoordinateScaling
open GammaRVChartPresentation GammaTranslation RVScaledRays RVNamedMultiplication
open GammaRVLifts GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def shiftVector {n : ℕ} (i : Fin n) (δ : Values.Gamma (M := M)) : Fin n → Values.Gamma (M := M) :=
  fun j => if j = i then δ else 1

def scaleAt {n : ℕ} (t : Code (M := M)) (i : Fin n) (z : Fin n → M) : Fin n → M :=
  fun j => if j = i then iRVMul (raw t) (z j) else z j

theorem scaleAt_proper {n : ℕ} (t : Code (M := M)) (i : Fin n) (z : Fin n → M) (hz : Proper z) :
    Proper (scaleAt t i z) := by
  intro j
  by_cases h : j = i
  · change NonzeroRV (if j = i then iRVMul (raw t) (z j) else z j)
    rw [ite_eq_left h]
    exact scale_nonzero t (hz j)
  · change NonzeroRV (if j = i then iRVMul (raw t) (z j) else z j)
    rw [ite_eq_right h]
    exact hz j

theorem scaleAt_inverse {n : ℕ} (t : Code (M := M)) (i : Fin n) (z : Fin n → M) (hz : Proper z) :
    scaleAt t i (scaleAt (inverseCode t) i z) = z := by
  funext j
  by_cases h : j = i
  · simp only [scaleAt, ite_eq_left h]
    have he := congrFun (scale_inverse t ![z j] (hz j).1) 0
    exact he
  · simp only [scaleAt, ite_eq_right h]

theorem scaleAt_injective {n : ℕ} (t : Code (M := M)) (i : Fin n) :
    Set.InjOn (scaleAt t i) {z : Fin n → M | Proper z} := by
  intro z hz w hw he
  funext j
  have hh := congrFun he j
  by_cases h : j = i
  · simp only [scaleAt, ite_eq_left h] at hh
    have hs : scale (raw t) ![z j] = scale (raw t) ![w j] := by
      funext l
      fin_cases l
      exact hh
    exact congrFun (scale_injective t (hz j) (hw j) hs) 0
  · simpa only [scaleAt, ite_eq_right h] using hh

theorem scaleAt_contraction {n : ℕ} (t : Code (M := M)) (i : Fin n) (z : Fin n → M) (hz : Proper z) :
    codeValues (scaleAt t i z) = shift (shiftVector i (value t)) (codeValues z) := by
  funext j
  by_cases h : j = i
  · change codeValue (if j = i then iRVMul (raw t) (z j) else z j) =
      (if j = i then value t else 1) * codeValue (z j)
    rw [ite_eq_left h, ite_eq_left h, GammaGroupNames.codeValue_mul _ _ ⟨raw_rv t, raw_ne_zero t⟩ (hz j), codeValue_raw]
  · change codeValue (if j = i then iRVMul (raw t) (z j) else z j) =
      (if j = i then value t else 1) * codeValue (z j)
    rw [ite_eq_right h, ite_eq_right h, one_mul]

theorem scaleAt_sharp_bijective {n : ℕ} (t : Code (M := M)) (i : Fin n)
    (I : Set (Fin n → Values.Gamma (M := M))) :
    Set.BijOn (scaleAt t i) (sharp I) (sharp (translated (shiftVector i (value t)) I)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ⟨scaleAt_proper t i z hz.1, ⟨codeValues z, hz.2, (scaleAt_contraction t i z hz.1).symm⟩⟩
  · apply (scaleAt_injective t i).mono
    exact fun _ hz => hz.1
  · intro z hz
    let u := scaleAt (inverseCode t) i z
    have hu : Proper u := scaleAt_proper (inverseCode t) i z hz.1
    have he : scaleAt t i u = z := scaleAt_inverse t i z hz.1
    obtain ⟨w, hw, hwe⟩ := hz.2
    have hsame : codeValues u = w := by
      have hs : shift (shiftVector i (value t)) (codeValues u) = shift (shiftVector i (value t)) w := by
        rw [← scaleAt_contraction t i u hu, he, hwe]
      exact funext (fun j => mul_left_cancel (congrFun hs j))
    exact ⟨u, ⟨hu, hsame.symm ▸ hw⟩, he⟩

theorem shiftVector_definable (B : Base (M := M)) {n : ℕ} (i : Fin n) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (j : Fin n) :
    GammaDefinableClosureAtBase B (shiftVector i δ j) := by
  change GammaDefinableClosureAtBase B (if j = i then δ else 1)
  by_cases h : j = i
  · rw [ite_eq_left h]
    exact hδ
  · rw [ite_eq_right h]
    exact GammaGroupNames.one_definable_base B

theorem scaleAt_weight (B : Base (M := M)) {n : ℕ} (i : Fin n) (δ : Values.Gamma (M := M))
    (hδ : GammaDefinableClosureAtBase B δ) (c : GammaWeightedCharts.Chart B n)
    (t : Code (M := M)) (ht : value t = δ) (z : Fin n → M) (hz : z ∈ sharp c.support) :
    (RVSharpCharts.sharpChart c).correctedWeight z =
      (RVSharpCharts.sharpChart (GammaTranslationCharts.translatedChart B
        (shiftVector i δ) (shiftVector_definable B i δ hδ) c)).correctedWeight (scaleAt t i z) := by
  have hc := scaleAt_contraction t i z hz.1
  rw [ht] at hc
  have hv := (GammaTranslationCharts.translationVolumeIso B
    (shiftVector i δ) (shiftVector_definable B i δ hδ) c).volume_eq (codeValues z) hz.2
  change c.volume (codeValues z) * (∏ j, codeValues z j) =
    (GammaTranslationCharts.translatedChart B (shiftVector i δ) (shiftVector_definable B i δ hδ) c).volume
      (codeValues (scaleAt t i z)) * (∏ j, codeValues (scaleAt t i z) j)
  rw [hc]
  exact (eq_div_iff_mul_eq').mp hv

end DiamondIntegral.Section4.RVCoordinateScaling
