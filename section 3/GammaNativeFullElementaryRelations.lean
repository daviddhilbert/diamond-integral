import «section 3».GammaMeasuredFiniteHeadCongruence
import «section 3».GammaNativeDeletedHeadFiniteness
import «section 3».GammaNativeElementaryCongruence
import «section 3».GammaNativeFullWeightNormalization

/-! Every coordinate of a full-weight native elementary blowup satisfies
the original principal Gamma relation with its unchanged Gamma density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
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

theorem gammaNativeFullElementary_congruence
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
        (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)))) := by
  let V : GammaGroundMeasuredRVObject hc B (n+1) := ⟨Section5.nativeRVGroundObject U hfull,ω⟩
  have he := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show V ⟶ gammaNativeMeasuredNormalization U ω from gammaNativeFullWeightNormalizationHom U hfull ω))
  rw [← he]
  exact gammaMeasuredFiniteHead_principal_congruence V _ (gammaRVDeletedHeadMap V.underlying i)
    (gammaNativeDeletedHead_finite hκ hs h00 hr U hfull i hAd)
    (fun u j => V.underlying.nonzero u (i.succAbove j))
    (gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd)
    (gammaNativeElementary_weight hκ hs h00 hr U hfull ω i hAd)

end DiamondIntegral.Section3
