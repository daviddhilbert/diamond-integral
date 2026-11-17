import «section 3».GammaNativeAdditiveInvariants
import «section 3».GammaMeasuredFullFocusIsomorphism
import «section 3».GammaGeneralFocusPreparedDensity

/-! Full-focus comparison for every additive elementary invariant.
All point maps and retained-form identities are the existing checked
ones; this exposes the geometric argument's universal property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
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
variable {W : Type*} [AddCommMonoid W]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaAdditiveFullFocus_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W) (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {i : Fin (n+1)} {j : Fin (rvObjectArity U.object.obj)} (D : Focus A i j)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
    let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
    let η := ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V (η.comp (Section5.nativeRVGroundIso e).map) := by
  exact (hχ U ω i hAd).trans (gammaNativeAdditiveValue_hom χ _ _ _ _
    (gammaMeasuredFullFocusHom hκ hs h00 hr U h D hfull hAd hA hD ω)).symm

theorem gammaAdditiveFullFocus_prepared_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W) (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {i : Fin (n+1)} {j : Fin (rvObjectArity U.object.obj)} (D : Focus A i j)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
    let T := SpecialBijection.centripetal D
    let hT := gammaCentripetal_chain_definable D hA hD
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V
      (ω.comp (gammaPreparedRVLabelMap U h T hT V.object.property)) := by
  let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
  let T := SpecialBijection.centripetal D
  let hT := gammaCentripetal_chain_definable D hA hD
  let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
  let K := gammaPreparedRVLabelMap (hc := hc) U h T hT V.object.property
  have hmap (q : Section5.nativeRVGroundDomain (hc := hc) V) :
      K q = gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd ((Section5.nativeRVGroundIso e).map q) := by
    apply Subtype.ext
    rw [gammaNativeFullFocus_old_labels hκ hs h00 hr U h D hfull hAd hA hD q]
    exact gammaPreparedRVLabelMap_val U h T hT V.object.property q
  have hform : (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)).comp
      (Section5.nativeRVGroundIso e).map = ω.comp K := by
    apply GammaGroundMap.ext
    intro q
    exact congrArg ω (hmap q).symm
  have H := gammaAdditiveFullFocus_comparison hκ hs h00 hr χ hχ U h D hfull hAd hA hD ω
  change gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V (ω.comp K)
  rw [← hform]
  exact H

end DiamondIntegral.Section3
