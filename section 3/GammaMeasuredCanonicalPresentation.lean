import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.FiniteGammaLiteralCharts
import IntegrationSection6.VolumePreservingElementary

/-! Canonical labelling preserves the actual structural tuple and
transports arbitrary Gamma densities along its retained old labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
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

def gammaMeasuredCanonicalPresentationHom (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let V := gammaCanonicalAt U h hA
    let e := gammaCanonicalIsoAt U h hA
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization V (ω.comp (Section5.nativeRVGroundIso e).map))
      (gammaNativeMeasuredNormalization U ω) := by
  let V := gammaCanonicalAt U h hA
  let e := gammaCanonicalIsoAt U h hA
  let F := Section5.nativeRVGroundIso (hc := hc) e
  apply gammaNativeMeasuredNormalizationHom _ ω e
  intro u
  have hv : (Section5.nativeRVGroundVolume U (F.map u)).val =
      (Section5.nativeRVGroundVolume V u).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    exact @canonicalRVKeyIso_inv_volume M N hN Set.univ (n+1) U.object.obj
      (Section5.nativeRVGroundDomainEquiv V u)
  unfold gammaNativeCombinedWeight
  change (gammaGroundFormValue ω (F.map u)).val * _ = _
  rw [hv]

theorem gammaNativeCanonical_old_labels (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaCanonicalAt U h hA)) :
    ((Section5.nativeRVGroundIso (gammaCanonicalIsoAt U h hA)).map u).val =
      u.val ∘ Fin.natAdd (n+1) := by
  exact @canonicalRVKeyIso_inv_labels M N hN Set.univ (n+1) U.object.obj
    (Section5.nativeRVGroundDomainEquiv (gammaCanonicalAt U h hA) u)

end DiamondIntegral.Section3
