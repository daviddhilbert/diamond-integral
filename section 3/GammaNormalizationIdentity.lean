import «section 3».GammaNativeCombinedWeights
import «section 3».GammaIndexedEssentialLabels

/-! Identity on normalized labels is measured whenever the literal
structural volumes and Gamma form values agree there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaNormalizationIdentityHom
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (e : GammaGroundBijection
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U))
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)))
    (hLabel : ∀ u, HEq u.val (e.map u).val)
    (hVol : ∀ (u : Section5.nativeRVGroundDomain (hc := hc) U)
      (v : Section5.nativeRVGroundDomain (hc := hc) V), HEq u.val v.val →
      (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V v).val)
    (hForm : ∀ (u : Section5.nativeRVGroundDomain (hc := hc) U)
      (v : Section5.nativeRVGroundDomain (hc := hc) V), HEq u.val v.val → (ω u).val = (η v).val) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  refine ⟨e,fun u => ?_⟩
  apply Subtype.ext
  rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight]
  let a := gammaNativeHighLabelInclusion U u
  let b := gammaNativeHighLabelInclusion V (e.map u)
  have hLabels : HEq a.val b.val := hLabel u
  have hDensity : gammaGroundFormValue ω a = gammaGroundFormValue η b :=
    congrArg (cast (gammaCarrier hc)) (hForm a b hLabels)
  unfold gammaNativeCombinedWeight
  rw [show gammaGroundFormValue ω a = gammaGroundFormValue η b from hDensity,
    show (Section5.nativeRVGroundVolume U a).val = (Section5.nativeRVGroundVolume V b).val from
      hVol a b hLabels]

end DiamondIntegral.Section3
