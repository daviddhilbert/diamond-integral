import «section 3».GammaAdditiveFocusComparison
import «section 3».GammaGeneralFocusPreparedDensity
import «section 3».GammaMeasuredComplementPresentation
import «section 3».GammaNativeMeasuredPullbackPartitions
import IntegrationSection6.FiniteGammaPartialCharts

/-! Partial-focus comparison for every additive elementary invariant,
using the existing actual cut maps and measured presentation charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
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

theorem gammaAdditivePartialFocus_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W) (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (U : GammaObjectAt B Set.univ (n+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {i : Fin (n+1)} {j : Fin (rvObjectArity U.object.obj)} (D : Focus A i j)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let V := gammaPartialFocusImageAt hκ hs h00 hr U h D hA hD
    let T := SpecialBijection.centripetal D
    let hT := gammaCentripetal_chain_definable D hA hD
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V
      (ω.comp (gammaPreparedRVLabelMap U h T hT V.object.property)) := by
  let C := focusActiveSet D
  let E := focusInactiveSet D
  let L := liftLabelLocus C
  have hLsub := liftLabelLocus_subset h (focusActiveSet_subset D)
  have hCΓ := gamma_focusActiveSet D hA hD
  have hEΓ : GammaSetDefinable B (carrier E) := (gammaLogicInput B).sdiff hA hCΓ
  have hLΓ := (gammaActiveRVObject h D U.real_contains hA hD).domain_graph
  let R := gammaRestrictAt U L hLsub hLΓ
  let Q := gammaComplementAt U L hLΓ
  let jR := gammaNativeRestrictedLabelInclusion (hc := hc) U L hLsub hLΓ
  let jQ := gammaNativeRestrictedLabelInclusion (hc := hc) U
    (@complement M N Set.univ (n+1) U.object.obj L)
    (@complement_subset M N hN Set.univ (n+1) U.object.obj L)
    ((gammaLogicInput B).sdiff U.domain_graph hLΓ)
  let ωR := ω.comp jR
  let ωQ := ω.comp jQ
  have hAd : GammaAdmissible R.toGamma.toGammaRVObject i :=
    gammaActiveRVObject_admissible h D hκ hs hr U.real_contains hA hD
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A) h)
  have hCP := focusActiveSet_pullback D hAP
  have hEP := focusInactiveSet_pullback D hAP
  have hp := partialFocus_source_partition D
  have hd : Disjoint (carrier C) (carrier E) :=
    Set.disjoint_left.mpr (fun _ ha he => he.2 ha)
  have hDA := gamma_activeFocus D hA hD
  let VA := gammaFullFocusImageAt hκ hs h00 hr R (focusActiveRVObject_presents h D)
    (activeFocus D) (activeFocus_full D) hAd hCΓ hDA
  let VE := gammaComplementPresentationAt U h hp hd hCP hEP hLΓ hEΓ
  let V := gammaPartialFocusImageAt hκ hs h00 hr U h D hA hD
  let T := SpecialBijection.centripetal D
  let hT := gammaCentripetal_chain_definable D hA hD
  let TA := SpecialBijection.centripetal (activeFocus D)
  let hTA := gammaCentripetal_chain_definable (activeFocus D) hCΓ hDA
  let K := gammaPreparedRVLabelMap (hc := hc) U h T hT V.object.property
  let KA := gammaPreparedRVLabelMap (hc := hc) R (focusActiveRVObject_presents h D)
    TA hTA VA.object.property
  let β := ω.comp K
  have hVΓ := GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩
  have hVAΓ := GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal (activeFocus D)) ⟨hCΓ,hDA⟩
  have hAV : carrier (activeFocus D).etaImage ⊆ carrier D.etaImage :=
    fun _ h => (Set.ext_iff.mp (partialFocus_image_partition D) _).mpr (Or.inl h)
  have hEV : carrier E ⊆ carrier D.etaImage :=
    fun _ h => (Set.ext_iff.mp (partialFocus_image_partition D) _).mpr (Or.inr h)
  let iA := gammaNativePullbackLabelInclusion (hc := hc) (activeFocus D).etaImage D.etaImage
    hVAΓ hVΓ hAV VA.object.property V.object.property
  let iE := gammaNativePullbackLabelInclusion (hc := hc) E D.etaImage
    hEΓ hVΓ hEV VE.object.property V.object.property
  have hβA : ωR.comp KA = β.comp iA := by rfl
  let eE := gammaComplementIsoAt U h hp hd hCP hEP hLΓ hEΓ
  have hβE : ωQ.comp (Section5.nativeRVGroundIso eE).map = β.comp iE := by
    apply GammaGroundMap.ext
    intro q
    change ω (jQ ((Section5.nativeRVGroundIso eE).map q)) = ω (K (iE q))
    congr 1
    apply Subtype.ext
    change ((Section5.nativeRVGroundIso eE).map q).val = (K (iE q)).val
    rw [gammaNativeComplementPresentation_old_labels,gammaPreparedRVLabelMap_val]
    rfl
  have hSource := gammaNativeMeasuredClass_scissor U L hLsub hLΓ ω
  have hTarget := gammaNativeMeasuredPullback_partition_class (activeFocus D).etaImage D.etaImage E
    hVAΓ hVΓ hEΓ (partialFocus_image_partition D) (partialFocus_image_disjoint D)
    ((activeFocus D).etaImage_pullback hCP) VA.object.property V.object.property VE.object.property β
  have hActive := gammaAdditiveFullFocus_prepared_comparison hκ hs h00 hr χ hχ R (focusActiveRVObject_presents h D)
    (activeFocus D) (activeFocus_full D) hAd hCΓ hDA ωR
  change gammaNativeAdditiveValue χ R ωR =
    gammaNativeAdditiveValue χ VA (ωR.comp KA) at hActive
  rw [hβA] at hActive
  have hInactive := gammaGroundMeasuredRVClass_iso (asIso
    (show gammaNativeMeasuredNormalization VE (ωQ.comp (Section5.nativeRVGroundIso eE).map) ⟶
      gammaNativeMeasuredNormalization Q ωQ from
      gammaMeasuredComplementPresentationHom U h hp hd hCP hEP hLΓ hEΓ ωQ))
  rw [hβE] at hInactive
  have hs' := gammaMeasuredClass_additive_scissor χ _ _ _ hSource
  have ht' := gammaMeasuredClass_additive_scissor χ _ _ _ hTarget
  have he' := congrArg χ hInactive.symm
  exact hs'.symm.trans ((congrArg₂ (fun x y => x+y) hActive he').trans ht')

end DiamondIntegral.Section3
