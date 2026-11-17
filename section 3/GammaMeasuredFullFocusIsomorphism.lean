import «section 3».GammaNativeMeasuredIsomorphisms
import IntegrationSection6.FiniteGammaFocusCharts
import IntegrationSection6.OriginalFocusVolume

/-! The actual full-focus RV comparison preserves its structural volume
and arbitrary pulled-back Gamma form. It recovers the old label as the
literal tail of the image key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)

def gammaMeasuredFullFocusHom (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {i : Fin (n+1)} {j : Fin (rvObjectArity U.object.obj)} (D : Focus A i j)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let E := gammaElementaryAt hκ hs h00 hr U i hAd
    let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
    let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
    let η := ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization V (η.comp (Section5.nativeRVGroundIso e).map))
      (gammaNativeMeasuredNormalization E η) := by
  let E := gammaElementaryAt hκ hs h00 hr U i hAd
  let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
  let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
  let F := Section5.nativeRVGroundIso (hc := hc) e
  let η := ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)
  apply gammaNativeMeasuredNormalizationHom _ η e
  intro u
  have hv : (Section5.nativeRVGroundVolume E (F.map u)).val =
      (Section5.nativeRVGroundVolume V u).val := by
    rw [gammaNativeRVGroundVolume_value,gammaNativeRVGroundVolume_value]
    exact originalAdmissibleFocusBlowup_volume h D hfull (hAd.ordinary hκ hs h00 hr)
      (Section5.nativeRVGroundDomainEquiv V u)
  unfold gammaNativeCombinedWeight
  change (gammaGroundFormValue η (F.map u)).val * _ = _
  rw [hv]

theorem gammaNativeFullFocus_old_labels (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {i : Fin (n+1)} {j : Fin (rvObjectArity U.object.obj)} (D : Focus A i j)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD)) :
    (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd
      ((Section5.nativeRVGroundIso (gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD)).map u)).val =
      u.val ∘ Fin.natAdd (n+1) := by
  let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
  let a := Section5.nativeRVGroundDomainEquiv V u
  let blow := @originalAdmissibleFocusBlowup M sM hM Set.univ (n+1) U.object.obj A h i j D hfull
    (hAd.ordinary hκ hs h00 hr)
  let ei := @IntegrationInACVF.Section6.ElementaryBlowup.iso M N hN Set.univ (n+1)
    U.object.obj (originalFocusObject D) blow
  let b := @RVHom.map M N Set.univ (n+1) _ _ ei.hom a
  have hk := originalAdmissibleFocusBlowup_key h D hfull (hAd.ordinary hκ hs h00 hr) a
  have hp := @elementaryProjection_labels M N hN Set.univ (n+1) U.object.obj i b
  rw [gammaNativeElementaryOldLabel_val]
  change b.val ∘ Fin.castAdd 1 = u.val ∘ Fin.natAdd (n+1)
  funext k
  have ht := congrArg (fun t => t (Fin.natAdd (n+1) k)) hk
  exact (congrFun hp k).symm.trans ((Fin.append_right _ _ k).symm.trans ht)

end DiamondIntegral.Section3
