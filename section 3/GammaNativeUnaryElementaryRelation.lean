import «section 3».GammaNativeElementaryCongruence
import «section 3».GammaNativeFullWeightNormalization

/-! Every actual unary elementary blowup, with its unchanged original
Gamma density, belongs to the stated special congruence after native
full-weight normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaNativeUnaryElementary_congruence
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject 0) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVSemiringClass
        (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U 0 hAd)
          (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U 0 hAd)))) := by
  let hfull := gammaUnaryAdmissible_full U hAd
  have he := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show (⟨Section5.nativeRVGroundObject U hfull,ω⟩ : GammaGroundMeasuredRVObject hc B 1) ⟶
      gammaNativeMeasuredNormalization U ω from gammaNativeFullWeightNormalizationHom U hfull ω))
  rw [← he]
  exact gammaNativeElementary_principal_congruence hκ hs h00 hr U hfull ω hAd

end DiamondIntegral.Section3
