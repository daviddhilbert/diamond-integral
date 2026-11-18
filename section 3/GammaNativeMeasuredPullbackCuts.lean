import «section 3».GammaNativePullbackCuts

/-! Literal mixed subsets induce measured RV cuts with exactly the
restricted Gamma form on their full-key presentations. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

def gammaNativePullbackLabelInclusion
    (C D : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (hC : GammaSetDefinable B (carrier C)) (hD : GammaSetDefinable B (carrier D))
    (hCD : carrier C ⊆ carrier D)
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D))) :
    GammaGroundMap (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) C hC hCF))
      (Section5.nativeRVGroundDomain (hc := hc) (gammaPullbackAt (Set.subset_univ _) D hD hDF)) :=
  gammaNativeRestrictedLabelInclusion (gammaPullbackAt (Set.subset_univ _) D hD hDF)
    (rvObjectDomain (pullbackObject C)) (gammaNativePullbackCut_subset C D hCD)
    (gammaPullbackAt (Set.subset_univ _) C hC hCF).domain_graph

def gammaNativeMeasuredPullbackCutHom
    (C D : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (hC : GammaSetDefinable B (carrier C)) (hD : GammaSetDefinable B (carrier D))
    (hCD : carrier C ⊆ carrier D)
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaPullbackAt (Set.subset_univ _) D hD hDF))) :
    let P := gammaPullbackAt (Set.subset_univ _) D hD hDF
    let Q := gammaPullbackAt (Set.subset_univ _) C hC hCF
    GammaGroundMeasuredRVHom
      ((gammaNativeMeasuredNormalization P ω).restrict
        ((Section5.nativeRVGroundDomain (gammaHighRestrictionAt P)).inter
          (Section5.nativeRVGroundDomain Q)) (fun _ h => h.1))
      (gammaNativeMeasuredNormalization Q (ω.comp (gammaNativePullbackLabelInclusion C D hC hD hCD hCF hDF))) :=
  gammaNativeMeasuredRestrictionHom (gammaPullbackAt (Set.subset_univ _) D hD hDF)
    (rvObjectDomain (pullbackObject C)) (gammaNativePullbackCut_subset C D hCD)
    (gammaPullbackAt (Set.subset_univ _) C hC hCF).domain_graph ω

end DiamondIntegral.Section3
