import «section 3».GammaNativeMeasuredPullbackCuts
import IntegrationSection6.PullbackPartitions

/-! A disjoint mixed pullback partition gives the literal complementary
full-key RV domain. -/
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

theorem gammaNativePullbackComplement_domain
    (C D E : SpecialTransformations.Section5.DefSet (M := M) Set.univ n a)
    (hC : GammaSetDefinable B (carrier C)) (hD : GammaSetDefinable B (carrier D))
    (hE : GammaSetDefinable B (carrier E))
    (hCover : carrier D = carrier C ∪ carrier E) (hCE : Disjoint (carrier C) (carrier E))
    (hCP : IsRVPullback (carrier C))
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (hEF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject E))) :
    let PC := gammaPullbackAt (Set.subset_univ _) C hC hCF
    let PD := gammaPullbackAt (Set.subset_univ _) D hD hDF
    let PE := gammaPullbackAt (Set.subset_univ _) E hE hEF
    (Section5.nativeRVGroundDomain (hc := hc)
      (gammaComplementAt PD (rvObjectDomain PC.object.obj) PC.domain_graph)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) PE).carrier := by
  dsimp only
  rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier]
  have hu := pullbackObject_domains_union hCover
  have hd := pullbackObject_domains_disjoint hCE hCP
  ext q
  constructor
  · rintro ⟨hq,hn⟩
    rcases (Set.ext_iff.mp hu q).mp hq with h | h
    · exact (hn h).elim
    · exact h
  · intro hq
    exact ⟨(Set.ext_iff.mp hu q).mpr (Or.inr hq),fun h => Set.disjoint_left.mp hd h hq⟩

end DiamondIntegral.Section3
