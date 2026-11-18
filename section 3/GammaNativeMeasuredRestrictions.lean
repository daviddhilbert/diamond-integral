import «section 3».GammaNativeHighRestrictions
import «section 3».GammaNativeCombinedWeights

/-! Normalization commutes with RV cuts as an actual measured RV
isomorphism, retaining the entire original Gamma form. -/
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
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)


def gammaNativeMeasuredRestrictionHom
    (U : GammaObjectAt B Set.univ (n+1))
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A) ⊆ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
  (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) Set.univ A})
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (hc := hc) U)) :
    GammaGroundMeasuredRVHom
      ((gammaNativeMeasuredNormalization U ω).restrict
        ((Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).inter
          (Section5.nativeRVGroundDomain (hc := hc) (gammaRestrictAt U A hA hAΓ))) (fun _ h => h.1))
      (gammaNativeMeasuredNormalization (gammaRestrictAt U A hA hAΓ)
        (ω.comp (gammaNativeRestrictedLabelInclusion U A hA hAΓ))) where
  bijection := GammaGroundBijection.ofCarrierEq (gammaNativeHighRestriction_domain U A hA hAΓ).symm
  preserves u := by
    let R := gammaRestrictAt U A hA hAΓ
    let a : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U) := ⟨u.val,u.property.1⟩
    let b : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt R) :=
      (GammaGroundBijection.ofCarrierEq (gammaNativeHighRestriction_domain U A hA hAΓ).symm).map u
    have hv : (Section5.nativeRVGroundVolume (gammaHighRestrictionAt U) a).val =
        (Section5.nativeRVGroundVolume (gammaHighRestrictionAt R) b).val := by
      rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
      rfl
    change gammaGroundFormValue _ u * _ = gammaGroundFormValue _ b * _
    have hf : gammaGroundFormValue
        (((gammaNativeMeasuredNormalization U ω).restrict
          ((Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).inter
            (Section5.nativeRVGroundDomain (hc := hc) R)) (fun _ h => h.1)).form) u =
        gammaGroundFormValue
          (gammaNativeMeasuredNormalization R (ω.comp (gammaNativeRestrictedLabelInclusion U A hA hAΓ))).form b := rfl
    rw [hf]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    apply Subtype.ext
    exact congrFun hv j

end DiamondIntegral.Section3
