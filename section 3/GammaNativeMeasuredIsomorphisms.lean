import «section 3».GammaNativeHighIsomorphisms
import «section 3».GammaNativeCombinedWeights

/-! Native original-Gamma isomorphisms with the actual Gamma weight
equation induce arrows in the local measured RV category after removing
zero structural labels. -/
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
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {U V : GammaObjectAt B Set.univ (n+1)}

theorem gammaNativeHighIso_square (e : GammaIsoAt U V)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)) :
    gammaNativeHighLabelInclusion V
      ((Section5.nativeRVGroundIso (gammaNativeHighRestrictionIso e)).map u) =
      (Section5.nativeRVGroundIso e).map (gammaNativeHighLabelInclusion U u) := by
  apply Subtype.ext
  rfl

def gammaNativeMeasuredNormalizationHom
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (e : GammaIsoAt U V)
    (hw : ∀ u, gammaNativeCombinedWeight U ω u =
      gammaNativeCombinedWeight V η ((Section5.nativeRVGroundIso e).map u)) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) where
  bijection := Section5.nativeRVGroundIso (gammaNativeHighRestrictionIso e)
  preserves u := by
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight,
      gammaNativeHighIso_square]
    exact hw (gammaNativeHighLabelInclusion U u)

end DiamondIntegral.Section3
