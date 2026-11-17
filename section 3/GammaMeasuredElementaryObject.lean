import «section 3».GammaMeasuredElementaryDomain
import «section 3».GammaMeasuredElementaryCongruence
import «section 3».GammaMeasuredHeadFiniteness

/-! The actual full-weight native elementary presentation carries the
weighted point/cone relation over the original Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
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

def gammaMeasuredElementaryChart (U : GammaGroundRVObject hc B (n+1))
    (i : Fin (n+1)) (hAd : GammaAdmissible (Section5.groundRVAt U).toGamma.toGammaRVObject i) :
    GammaGroundBijection
      (Section5.nativeRVGroundDomain (gammaHighRestrictionAt
        (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U) i hAd)))
      (U.domain.prod (gammaGroundMeasuredRVPositive hc B).underlying.domain) :=
  (gammaGroundRVPackBijection U.domain (gammaGroundMeasuredRVPositive hc B).underlying.domain).symm.comp
    (GammaGroundBijection.ofCarrierEq (gammaMeasuredElementary_positive_domain hκ hs h00 hr U i hAd))

def gammaMeasuredElementaryWeight (U : GammaGroundMeasuredRVObject hc B (n+1))
    (i : Fin (n+1)) (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaHighRestrictionAt
      (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd))) :=
  GammaGroundVolumeForm.mul (U.combinedWeightForm.comp ((GammaGroundMap.prodFst _ _).comp
    (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map))
  ((gammaGroundMeasuredRVPositive hc B).combinedWeightForm.comp ((GammaGroundMap.prodSnd _ _).comp
    (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map))

def gammaMeasuredElementaryObject (U : GammaGroundMeasuredRVObject hc B (n+1))
    (i : Fin (n+1)) (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    GammaGroundMeasuredRVObject hc B (n+1) :=
  (Section5.nativeRVGroundObject (gammaHighRestrictionAt
    (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd))
      (gammaHighRestriction_fullWeight _)).withCombinedWeight
    (gammaMeasuredElementaryWeight hκ hs h00 hr U i hAd)

theorem gammaMeasuredElementaryObject_weight (U : GammaGroundMeasuredRVObject hc B (n+1))
    (i : Fin (n+1)) (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) :
    (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).combinedWeight w =
      U.combinedWeight ⟨((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.1,
        ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).property.1⟩ *
      (gammaGroundMeasuredRVPositive hc B).combinedWeight
        ⟨((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.2,
          ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).property.2⟩ := by
  unfold gammaMeasuredElementaryObject
  rw [GammaGroundRVObject.withCombinedWeight_value]
  exact congrArg₂ (· * ·) (U.combinedWeightForm_value _) ((gammaGroundMeasuredRVPositive hc B).combinedWeightForm_value _)

theorem gammaMeasuredElementaryObject_congruence (U : GammaGroundMeasuredRVObject hc B (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject (Fin.last n)) :
    gammaGroundMeasuredRVSpecialCongruence hc B (gammaGroundMeasuredRVSemiringClass U)
      (gammaGroundMeasuredRVSemiringClass (gammaMeasuredElementaryObject hκ hs h00 hr U (Fin.last n) hAd)) :=
  gammaMeasuredElementary_principal_congruence U _
    (gammaMeasuredHead_finite_of_admissible hκ hs h00 hr U.underlying hAd)
    (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying (Fin.last n) hAd)
    (gammaMeasuredElementaryObject_weight hκ hs h00 hr U (Fin.last n) hAd)

end DiamondIntegral.Section3
