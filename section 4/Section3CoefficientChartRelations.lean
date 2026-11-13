import «section 4».Section3TensorComparisonSquares
import «section 4».GammaOrdinaryTranslations
import «section 4».RVCoordinateScaling

/-! Native coefficient pairs become the chart translation relations,
including the compensation of the original measured volume. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
open scoped TensorProduct

namespace DiamondIntegral.Section4.Section3CoefficientChartRelations
open Section3GammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem shifted_support {n : ℕ} (G H : GammaGroundGammaPiece hc B n) (delta : Fin n → Values.Gamma (M := M))
    (hs : ∀ g : Fin n → Values.Gamma (M := M), g ∈ G.carrier ↔ (fun j => delta j * g j) ∈ H.carrier) :
    GammaTranslation.translated delta G.carrier = H.carrier := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hs g).mp hg
  · intro hz
    let g := fun j => (delta j)⁻¹ * z j
    have he : GammaTranslation.shift delta g = z := by funext j; exact mul_inv_cancel_left _ _
    have hg : (fun j => delta j * g j) ∈ H.carrier := by
      change GammaTranslation.shift delta g ∈ H.carrier
      rw [he]
      exact hz
    exact ⟨g, (hs g).mpr hg, he⟩

theorem ordinary_translated {n : ℕ} (G H : GammaGroundGammaPiece hc B n) (delta : Fin n → Values.Gamma (M := M))
    (hd : ∀ j, GammaDefinableClosureAtBase B (delta j))
    (hs : ∀ g : Fin n → Values.Gamma (M := M), g ∈ G.carrier ↔ (fun j => delta j * g j) ∈ H.carrier) :
    GammaOrdinaryRing.objectClass (GammaOrdinaryTranslations.translatedChart B delta hd (chart G)) =
      GammaOrdinaryRing.objectClass (chart H) :=
  GammaOrdinaryRing.class_iso (GammaOrdinaryCharts.sameSupportIso _ _ (shifted_support G H delta hs))

def weightChart {n : ℕ} (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f) :
    GammaWeightedCharts.Chart B n := measuredChart G ((gammaGroundMeasuredGammaSingleWeight G f hf).form (0 : Fin 1))

theorem weightChart_weight {n : ℕ} (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : γ ∈ G.carrier) :
    (weightChart G f hf).volume γ * ∏ i, γ i = f γ := by
  have h := measuredChart_volume G ((gammaGroundMeasuredGammaSingleWeight G f hf).form (0 : Fin 1)) ⟨γ, hγ⟩
  exact (congrArg (fun t => t * ∏ i, γ i) h).trans
    (gammaGroundMeasuredGammaSingleWeight_combined G f hf ⟨(0 : Fin 1), ⟨γ, hγ⟩⟩)

theorem measured_translated {n : ℕ} (G H : GammaGroundGammaPiece hc B n)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (hh : FullGammaFunction (integrationGammaBase B) h)
    (delta : Fin n → Values.Gamma (M := M)) (hd : ∀ j, GammaDefinableClosureAtBase B (delta j))
    (hs : ∀ g : Fin n → Values.Gamma (M := M), g ∈ G.carrier ↔ (fun j => delta j * g j) ∈ H.carrier)
    (hw : ∀ g : Fin n → Values.Gamma (M := M), g ∈ G.carrier → f g = h (fun j => delta j * g j)) :
    GammaRVChartPresentation.objectClass (GammaTranslationCharts.translatedChart B delta hd (weightChart G f hf)) =
      GammaRVChartPresentation.objectClass (weightChart H h hh) := by
  apply GammaRVIdentityIso.class_eq_on_domain _ _ (shifted_support G H delta hs)
  rintro _ ⟨g, hg, rfl⟩
  apply mul_right_cancel (b := ∏ j, delta j * g j)
  have ht := (GammaTranslationCharts.translationVolumeIso B delta hd (weightChart G f hf)).volume_eq g hg
  calc
    _ = (weightChart G f hf).volume g * ∏ j, g j := ((eq_div_iff_mul_eq').mp ht).symm
    _ = f g := weightChart_weight G f hf g hg
    _ = h (fun j => delta j * g j) := hw g hg
    _ = _ := (weightChart_weight H h hh _ ((hs g).mp hg)).symm

theorem shiftVector_eq {n : ℕ} (i : Fin n) (delta : Fin n → Values.Gamma (M := M))
    (h : ∀ j, j ≠ i → delta j = 1) : RVCoordinateScaling.shiftVector i (delta i) = delta := by
  funext j
  by_cases hj : j = i
  · subst j; simp only [RVCoordinateScaling.shiftVector, ite_true]
  · simp only [RVCoordinateScaling.shiftVector, ite_eq_right hj, h j hj]

end DiamondIntegral.Section4.Section3CoefficientChartRelations
