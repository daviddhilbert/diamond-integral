import «section 4».GammaTranslationCharts
import «section 4».GammaFiniteBounds

/-! Compensated Gamma translations preserve actual double bounds,
including in non-Archimedean groups and in degree zero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedTranslationCharts
open GammaBoundedProducts GammaTranslation GammaTranslationCharts GammaWeightedCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem translated_bounded {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : DomainBounded I) : DomainBounded (translated a I) := by
  obtain ⟨β, hβ⟩ := hI
  obtain ⟨α, hα⟩ := GammaFiniteBounds.singleton_bounded a
  refine ⟨α * β, ?_⟩
  rintro z ⟨x, hx, rfl⟩ i
  change (α * β)⁻¹ ≤ a i * x i ∧ a i * x i ≤ α * β
  constructor
  · simpa only [mul_inv] using mul_le_mul' (hα a (Set.mem_singleton a) i).1 (hβ x hx i).1
  · exact mul_le_mul' (hα a (Set.mem_singleton a) i).2 (hβ x hx i).2

def translatedChart (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaBoundedRVCharts.BoundedChart B n) : GammaBoundedRVCharts.BoundedChart B n :=
  ⟨GammaTranslationCharts.translatedChart B a ha c.toChart, translated_bounded a c.support c.domain_bounded⟩

def translationVolumeIso (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaBoundedRVCharts.BoundedChart B n) : VolumeIso c.toChart (translatedChart B a ha c).toChart :=
  GammaTranslationCharts.translationVolumeIso B a ha c.toChart

end DiamondIntegral.Section4.GammaBoundedTranslationCharts
