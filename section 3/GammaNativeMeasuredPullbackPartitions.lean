import «section 3».GammaNativeMeasuredPullbackComplements
import «section 3».GammaNativeMeasuredScissors

/-! A literal mixed pullback partition gives the exact measured RV
scissor equality with an arbitrary Gamma density on the whole full key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
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

theorem gammaNativeMeasuredPullback_partition_class
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
    let hCD : carrier C ⊆ carrier D := fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inl h)
    let hED : carrier E ⊆ carrier D := fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inr h)
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization PC
      (ω.comp (gammaNativePullbackLabelInclusion C D hC hD hCD hCF hDF))) +
      gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization PE
        (ω.comp (gammaNativePullbackLabelInclusion E D hE hD hED hEF hDF))) =
      gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization PD ω) := by
  let PC := gammaPullbackAt (Set.subset_univ _) C hC hCF
  let PD := gammaPullbackAt (Set.subset_univ _) D hD hDF
  let PE := gammaPullbackAt (Set.subset_univ _) E hE hEF
  let hCD : carrier C ⊆ carrier D := fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inl h)
  let hED : carrier E ⊆ carrier D := fun _ h => (Set.ext_iff.mp hCover _).mpr (Or.inr h)
  let J := @complement M N Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
  let hJ := @complement_subset M N hN Set.univ (n+1) PD.object.obj (rvObjectDomain PC.object.obj)
  let hJΓ := (gammaLogicInput B).sdiff PD.domain_graph PC.domain_graph
  let Q := gammaComplementAt PD (rvObjectDomain PC.object.obj) PC.domain_graph
  let ωQ := ω.comp (gammaNativeRestrictedLabelInclusion PD J hJ hJΓ)
  let ωC := ω.comp (gammaNativePullbackLabelInclusion C D hC hD hCD hCF hDF)
  let ωE := ω.comp (gammaNativePullbackLabelInclusion E D hE hD hED hEF hDF)
  have H := gammaNativeMeasuredClass_scissor PD (rvObjectDomain PC.object.obj)
    (gammaNativePullbackCut_subset C D hCD) PC.domain_graph ω
  have he := gammaGroundMeasuredRVClass_iso (asIso
    (show gammaNativeMeasuredNormalization Q ωQ ⟶ gammaNativeMeasuredNormalization PE ωE from
      gammaNativeMeasuredPullbackComplementHom C D E hC hD hE hCover hCE hCP hCF hDF hEF ω))
  change gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization PC ωC) +
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization Q ωQ) =
    gammaGroundMeasuredRVClass (gammaNativeMeasuredNormalization PD ω) at H
  rw [he] at H
  exact H

end DiamondIntegral.Section3
