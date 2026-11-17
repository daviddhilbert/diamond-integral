import «section 3».GammaNativeGroundIsomorphisms
import «section 3».GammaNativeMeasuredIsomorphisms

/-! A literal native label bijection preserving structural volume and
Gamma density gives the same measured arrow after normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaNativeMeasuredGroundHom
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hv : ∀ u, (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V (f.map u)).val)
    (hω : ∀ u, gammaGroundFormValue ω u = gammaGroundFormValue η (f.map u)) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  apply gammaNativeMeasuredNormalizationHom ω η (gammaNativeIsoOfGroundBijection U V f hv)
  intro u
  rw [gammaNativeIsoOfGroundBijection_map]
  unfold gammaNativeCombinedWeight
  rw [hω u,← hv u]

end DiamondIntegral.Section3
