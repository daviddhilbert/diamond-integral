import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.FiniteGammaPresentationCharts
import Integration7.VolumePullbackPresentations

/-! Literal RV-pullback presentation isomorphisms preserve arbitrary
Gamma forms pulled back along their old-label projection. -/
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaMeasuredPresentationHom (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaPresentationAt U h hA)
        (ω.comp (Section5.nativeRVGroundIso (gammaPresentationIsoAt U h hA)).map))
      (gammaNativeMeasuredNormalization U ω) := by
  let P := gammaPresentationAt U h hA
  let e := gammaPresentationIsoAt U h hA
  let F := Section5.nativeRVGroundIso (hc := hc) e
  apply gammaNativeMeasuredNormalizationHom _ ω e
  intro u
  have hv : (Section5.nativeRVGroundVolume U (F.map u)).val =
      (Section5.nativeRVGroundVolume P u).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    exact IntegrationInACVF.Section7.pullbackPresentation_volume h
      (Section5.nativeRVGroundDomainEquiv P u)
  unfold gammaNativeCombinedWeight
  change (gammaGroundFormValue ω (F.map u)).val * _ = _
  rw [hv]

end DiamondIntegral.Section3
