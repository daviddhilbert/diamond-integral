import «section 3».GammaNativeMeasuredNormalization
import «section 3».GammaMeasuredElementaryForm

/-! The full Gamma weight can be evaluated on native RV presentations,
including zero structural labels. On their full-weight parts this is
exactly the local category's combined weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
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

def gammaNativeCombinedWeight (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (u : Section5.nativeRVGroundDomain (hc := hc) U) : Values.GammaTop (M := M) :=
  (gammaGroundFormValue ω u).val * ∏ j, Values.vrv ((Section5.nativeRVGroundVolume U u).val j)

theorem gammaNativeHigh_groundVolume (U : GammaObjectAt B Set.univ (n+1))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)) :
    (Section5.nativeRVGroundVolume U (gammaNativeHighLabelInclusion U u)).val =
      (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) u).val := by
  rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
  rfl

theorem gammaNativeMeasuredNormalization_weight (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (u : (gammaNativeMeasuredNormalization U ω).underlying.domain) :
    ((gammaNativeMeasuredNormalization U ω).combinedWeight u).val =
      gammaNativeCombinedWeight U ω (gammaNativeHighLabelInclusion U u) := by
  let V := gammaNativeMeasuredNormalization U ω
  change (gammaGroundFormValue V.form u * ∏ j, Section2.rvFiniteValue (V.underlying.target u j)).val = _
  rw [Values.gamma_val_mul]
  have hw : (∏ j, Section2.rvFiniteValue (V.underlying.target u j)).val =
      ∏ j, Values.vrv ((V.underlying.volume u).val j) := by
    change Values.gammaValHom (∏ j, Section2.rvFiniteValue (V.underlying.target u j)) = _
    rw [map_prod]
    rfl
  rw [hw]
  change (gammaGroundFormValue ω (gammaNativeHighLabelInclusion U u)).val *
      ∏ j, Values.vrv ((Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) u).val j) = _
  unfold gammaNativeCombinedWeight
  rw [gammaNativeHigh_groundVolume]

end DiamondIntegral.Section3
