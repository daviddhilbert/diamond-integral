import «section 3».GammaNativeElementaryHighComparison
import «section 3».GammaNativeCombinedWeights

/-! Removing zero source coordinates commutes with the actual elementary
Gamma density and its complete structural volume. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
variable (U : GammaObjectAt B Set.univ (n+1)) (i : Fin (n+1))
variable (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
local notation "EU" => gammaElementaryAt hκ hs h00 hr U i hAd
local notation "EH" => gammaElementaryAt hκ hs h00 hr (gammaHighRestrictionAt U) i (gammaNativeHigh_admissible U i hAd)

def gammaNativeElementaryHighMeasuredHom
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (EH)
        ((ω.comp (gammaNativeHighLabelInclusion U)).comp
          (gammaNativeElementaryOldLabel hκ hs h00 hr (gammaHighRestrictionAt U) i (gammaNativeHigh_admissible U i hAd))))
      (gammaNativeMeasuredNormalization (EU) (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))) where
  bijection := gammaNativeElementaryHighBijection hκ hs h00 hr U i hAd
  preserves := by
    intro w
    let g := gammaNativeElementaryHighBijection (hc := hc) hκ hs h00 hr U i hAd
    have hv : (Section5.nativeRVGroundVolume (EU) (gammaNativeHighLabelInclusion (EU) (g.map w))).val =
        (Section5.nativeRVGroundVolume (EH) (gammaNativeHighLabelInclusion (EH) w)).val :=
      (gammaNativeHigh_groundVolume (EU) (g.map w)).trans
        ((gammaNativeElementaryHighBijection_volume hκ hs h00 hr U i hAd w).trans
          (gammaNativeHigh_groundVolume (EH) w).symm)
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight]
    unfold gammaNativeCombinedWeight
    rw [hv]
    rfl

end DiamondIntegral.Section3
