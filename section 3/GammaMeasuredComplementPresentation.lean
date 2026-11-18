import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.FiniteGammaComplementCharts
import Integration7.VolumePullbackPresentations

/-! The inactive part of a partial focus preserves its structural RV tuple
and every Gamma density pulled back through its actual label projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

def gammaMeasuredComplementPresentationHom (U : GammaObjectAt B Set.univ (n+1))
    {A C E : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hp : carrier A = carrier C ∪ carrier E) (hd : Disjoint (carrier C) (carrier E))
    (hC : IsRVPullback (carrier C)) (hE : IsRVPullback (carrier E))
    (hLΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @DefSet.carrier LRV M N _ Set.univ (liftLabelLocus C)})
    (hEΓ : GammaSetDefinable B (carrier E))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaComplementAt U (liftLabelLocus C) hLΓ))) :
    let V := gammaComplementPresentationAt U h hp hd hC hE hLΓ hEΓ
    let Q := gammaComplementAt U (liftLabelLocus C) hLΓ
    let e := gammaComplementIsoAt U h hp hd hC hE hLΓ hEΓ
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization V (ω.comp (Section5.nativeRVGroundIso e).map))
      (gammaNativeMeasuredNormalization Q ω) := by
  let V := gammaComplementPresentationAt U h hp hd hC hE hLΓ hEΓ
  let Q := gammaComplementAt U (liftLabelLocus C) hLΓ
  let e := gammaComplementIsoAt U h hp hd hC hE hLΓ hEΓ
  let F := Section5.nativeRVGroundIso (hc := hc) e
  have hEA : carrier E ⊆ carrier A := fun p hpE => (Set.ext_iff.mp hp p).mpr (Or.inr hpE)
  have hRep := normalizedPresentsLift_sublocus h hEA hE
  apply gammaNativeMeasuredNormalizationHom _ ω e
  intro u
  have hv : (Section5.nativeRVGroundVolume Q (F.map u)).val =
      (Section5.nativeRVGroundVolume V u).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    exact IntegrationInACVF.Section7.pullbackPresentation_volume hRep
      (Section5.nativeRVGroundDomainEquiv V u)
  unfold gammaNativeCombinedWeight
  change (gammaGroundFormValue ω (F.map u)).val * _ = _
  rw [hv]

theorem gammaNativeComplementPresentation_old_labels (U : GammaObjectAt B Set.univ (n+1))
    {A C E : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    (hp : carrier A = carrier C ∪ carrier E) (hd : Disjoint (carrier C) (carrier E))
    (hC : IsRVPullback (carrier C)) (hE : IsRVPullback (carrier E))
    (hLΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @DefSet.carrier LRV M N _ Set.univ (liftLabelLocus C)})
    (hEΓ : GammaSetDefinable B (carrier E))
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaComplementPresentationAt U h hp hd hC hE hLΓ hEΓ)) :
    ((Section5.nativeRVGroundIso (gammaComplementIsoAt U h hp hd hC hE hLΓ hEΓ)).map u).val =
      u.val ∘ Fin.natAdd (n+1) := by
  exact liftComplementIso_labels h hp hd hC hE
    (Section5.nativeRVGroundDomainEquiv (gammaComplementPresentationAt U h hp hd hC hE hLΓ hEΓ) u)

end DiamondIntegral.Section3
