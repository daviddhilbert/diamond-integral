import «section 3».GammaNativeFullElementaryRelations
import «section 3».GammaNativeElementaryHighMeasure

/-! Every actual native elementary blowup in every positive degree
respects the original principal Gamma congruence, with arbitrary original
Gamma density and without assuming full structural weight at the source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeElementary_congruence
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
        (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)))) := by
  let H := gammaHighRestrictionAt U
  let ρ := ω.comp (gammaNativeHighLabelInclusion U)
  let hAdH := gammaNativeHigh_admissible U i hAd
  have hSource := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show gammaNativeMeasuredNormalization U ω ⟶ gammaNativeMeasuredNormalization H ρ from
      gammaNativeFullWeightNormalizationHom H (gammaHighRestriction_fullWeight U) ρ))
  have hElem := gammaNativeFullElementary_congruence hκ hs h00 hr H (gammaHighRestriction_fullWeight U) ρ i hAdH
  have hTarget := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show gammaNativeMeasuredNormalization _ _ ⟶ gammaNativeMeasuredNormalization _ _ from
      gammaNativeElementaryHighMeasuredHom hκ hs h00 hr U i hAd ω))
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  apply (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mp
  exact (congrArg q hSource).trans
    (((gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr hElem).trans (congrArg q hTarget))

end DiamondIntegral.Section3
