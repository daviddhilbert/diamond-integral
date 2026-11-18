import «section 3».GammaNativeMeasuredRestrictions
import «section 3».GammaNativePullbackForms

/-! A literal subset of mixed tuples gives the literal full-key RV cut.
Its structural projection is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativePullbackCut_subset
    (C D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
    (hCD : carrier C ⊆ carrier D) :
    (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain (pullbackObject C))) ⊆
      (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain (pullbackObject D))) := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,hCD p.property⟩,hp⟩

theorem gammaNativePullbackCut_object
    (C D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
    (hC : GammaSetDefinable B (carrier C)) (hD : GammaSetDefinable B (carrier D))
    (hCD : carrier C ⊆ carrier D)
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D))) :
    gammaRestrictAt (gammaPullbackAt (Set.subset_univ _) D hD hDF)
      (rvObjectDomain (pullbackObject C)) (gammaNativePullbackCut_subset C D hCD)
      (gammaPullbackAt (Set.subset_univ _) C hC hCF).domain_graph =
      gammaPullbackAt (Set.subset_univ _) C hC hCF := by
  rfl

end DiamondIntegral.Section3
