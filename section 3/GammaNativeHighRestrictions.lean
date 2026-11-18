import «section 3».GammaNativeMeasuredNormalization
import IntegrationSection6.FiniteGammaRestrictions

/-! Full-weight normalization commutes with an actual original-ground
RV restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
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


def gammaNativeRestrictedLabelInclusion
    (U : GammaObjectAt B Set.univ (n+1))
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A) ⊆ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A}) :
    GammaGroundMap (Section5.nativeRVGroundDomain (hc := hc) (gammaRestrictAt U A hA hAΓ))
      (Section5.nativeRVGroundDomain (hc := hc) U) :=
  GammaGroundMap.inclusion (fun _ hx => (Section5.nativeRVGroundDomain_carrier U).ge
    (hA ((Section5.nativeRVGroundDomain_carrier (gammaRestrictAt U A hA hAΓ)).le hx)))

theorem gammaNativeHighRestriction_domain
    (U : GammaObjectAt B Set.univ (n+1))
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A) ⊆ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A}) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaRestrictAt U A hA hAΓ))).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ∩
        (Section5.nativeRVGroundDomain (hc := hc) (gammaRestrictAt U A hA hAΓ)).carrier := by
  let R := gammaRestrictAt U A hA hAΓ
  have hlow (x) (hx : x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A) :
      x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n R.object.obj)) ↔
        x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n U.object.obj)) :=
    (@mem_rvLowDomain M N Set.univ n R.object.obj ⟨x,hx⟩).trans
      (@mem_rvLowDomain M N Set.univ n U.object.obj ⟨x,hA hx⟩).symm
  rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier,
    Section5.nativeRVGroundDomain_carrier]
  ext x
  change (x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A) ∧
    x ∉ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n R.object.obj))) ↔
      ((x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj)) ∧
        x ∉ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n U.object.obj))) ∧
          x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A))
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨⟨hA hx,fun h => hn ((hlow x hx).mpr h)⟩,hx⟩
  · rintro ⟨⟨_,hn⟩,hx⟩
    exact ⟨hx,fun h => hn ((hlow x hx).mp h)⟩

end DiamondIntegral.Section3
