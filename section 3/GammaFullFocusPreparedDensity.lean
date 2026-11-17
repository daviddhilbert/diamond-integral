import «section 3».GammaNativeFullFocusCongruence
import «section 3».GammaPreparedRVLabelMap

/-! The full-focus congruence uses exactly the original density evaluated
on the retained source labels, as in the prepared-chain RV object. -/
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

theorem gammaCentripetal_chain_definable {S : Set M} {n m : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m} {i : Fin n} {j : Fin m}
    (D : Focus A i j) (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaChainDefinable B (SpecialBijection.centripetal D).chain :=
  ⟨⟨hA,hD⟩,GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩⟩

theorem gammaFullFocus_prepared_congruence
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1)) (hweight : GammaFullWeightAt U)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet A))
    {j : Fin (rvObjectArity U.object.obj)} (D : Focus A (Fin.last n) j)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last n))
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
    let T := SpecialBijection.centripetal D
    let hT := gammaCentripetal_chain_definable D hA hD
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization V
        (ω.comp (gammaPreparedRVLabelMap U h T hT V.object.property)))) := by
  let V := gammaFullFocusImageAt hκ hs h00 hr U h D hfull hAd hA hD
  let T := SpecialBijection.centripetal D
  let hT := gammaCentripetal_chain_definable D hA hD
  let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
  let K := gammaPreparedRVLabelMap (hc := hc) U h T hT V.object.property
  have hmap (q : Section5.nativeRVGroundDomain (hc := hc) V) :
      K q = gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.last n) hAd
        ((Section5.nativeRVGroundIso e).map q) := by
    apply Subtype.ext
    rw [gammaNativeFullFocus_old_labels hκ hs h00 hr U h D hfull hAd hA hD q]
    exact gammaPreparedRVLabelMap_val U h T hT V.object.property q
  have hform : (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.last n) hAd)).comp
      (Section5.nativeRVGroundIso e).map = ω.comp K := by
    apply GammaGroundMap.ext
    intro q
    exact congrArg ω (hmap q).symm
  have H := gammaNativeFullFocus_congruence hκ hs h00 hr U hweight h D hfull hAd hA hD ω
  change gammaGroundMeasuredRVSpecialCongruence hc B
    (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
    (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization V (ω.comp K)))
  rw [← hform]
  exact H

end DiamondIntegral.Section3
