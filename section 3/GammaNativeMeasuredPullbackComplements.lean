import «section 3».GammaNativePullbackComplements
import «section 3».GammaNativeMeasuredGroundIsomorphisms

/-! Complementary full-key domains give actual measured RV identity
comparisons with the restricted original Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeMeasuredPullbackComplementHom
    (C D E : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (hC : GammaSetDefinable B (carrier C)) (hD : GammaSetDefinable B (carrier D))
    (hE : GammaSetDefinable B (carrier E))
    (hCover : carrier D = carrier C ∪ carrier E) (hCE : Disjoint (carrier C) (carrier E))
    (hCP : IsRVPullback (carrier C))
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (hEF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject E)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) D hD hDF))) :
    let PC := gammaPullbackAt (Set.subset_univ _) C hC hCF
    let PD := gammaPullbackAt (Set.subset_univ _) D hD hDF
    let PE := gammaPullbackAt (Set.subset_univ _) E hE hEF
    let J := @complement M N Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
    let hJ := @complement_subset M N hN Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
    let hJΓ := (gammaLogicInput B).sdiff PD.domain_graph PC.domain_graph
    let ωQ := ω.comp (gammaNativeRestrictedLabelInclusion PD J hJ hJΓ)
    let ωE := ω.comp (gammaNativePullbackLabelInclusion E D hE hD
      (fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inr h)) hEF hDF)
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaComplementAt PD (rvObjectDomain PC.object.obj) PC.domain_graph) ωQ)
      (gammaNativeMeasuredNormalization PE ωE) := by
  let PC := gammaPullbackAt (Set.subset_univ _) C hC hCF
  let PD := gammaPullbackAt (Set.subset_univ _) D hD hDF
  let PE := gammaPullbackAt (Set.subset_univ _) E hE hEF
  let Q := gammaComplementAt PD (rvObjectDomain PC.object.obj) PC.domain_graph
  let J := @complement M N Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
  let hJ := @complement_subset M N hN Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
  let hJΓ := (gammaLogicInput B).sdiff PD.domain_graph PC.domain_graph
  let ωQ := ω.comp (gammaNativeRestrictedLabelInclusion PD J hJ hJΓ)
  let ωE := ω.comp (gammaNativePullbackLabelInclusion E D hE hD
    (fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inr h)) hEF hDF)
  let f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) Q) (Section5.nativeRVGroundDomain PE) :=
    GammaGroundBijection.ofCarrierEq
      (gammaNativePullbackComplement_domain C D E hC hD hE hCover hCE hCP hCF hDF hEF)
  change GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization Q ωQ) (gammaNativeMeasuredNormalization PE ωE)
  apply gammaNativeMeasuredGroundHom Q PE ωQ ωE f
  · intro u
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    rfl
  · intro u
    rfl

end DiamondIntegral.Section3
