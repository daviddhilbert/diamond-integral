import «section 3».GammaNativeMeasuredNormalization
import «section 3».GammaMeasuredElementaryForm
import «section 3».GammaNativeMeasuredLiftBridge

/-! Normalizing the native elementary transported form gives exactly the
weighted elementary object used in the original special congruence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)

def gammaMeasuredElementaryNormalizationHom
    (U : GammaGroundMeasuredRVObject hc B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization
        (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd)
        ((U.form.comp (Section5.groundRVObjectRoundTrip U.underlying).map).comp
          (gammaNativeElementaryOldLabel hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd)))
      (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd) where
  bijection := GammaGroundBijection.id _
  preserves w := by
    let W := gammaMeasuredElementaryObject hκ hs h00 hr U i hAd
    let z := (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w
    let u : U.underlying.domain := ⟨z.val.1,z.property.1⟩
    have hleft : ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.1 =
        w.val ∘ Fin.castAdd 1 :=
      congrArg Prod.fst (gammaMeasuredElementaryChart_val hκ hs h00 hr U.underlying i hAd w)
    have hf : gammaGroundFormValue
        (gammaNativeMeasuredNormalization
          (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd)
          ((U.form.comp (Section5.groundRVObjectRoundTrip U.underlying).map).comp
            (gammaNativeElementaryOldLabel hκ hs h00 hr (Section5.groundRVAt U.underlying) i hAd))).form w =
        gammaGroundFormValue U.form u := by
      change gammaGroundFormValue U.form _ = gammaGroundFormValue U.form u
      congr 1
      apply Subtype.ext
      exact hleft.symm
    change gammaGroundFormValue _ w * _ = gammaGroundFormValue W.form w * _
    rw [hf,gammaMeasuredElementaryObject_form hκ hs h00 hr U i hAd w]
    rfl

end DiamondIntegral.Section3
