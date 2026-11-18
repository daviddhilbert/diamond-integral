import «section 3».GammaMeasuredFullFocusIsomorphism
import «section 3».GammaNativeElementaryCongruence
import «section 3».GammaNativeFullWeightNormalization

/-! The actual full-focus image has the original special-congruence
class with its transported arbitrary Gamma density. -/
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

theorem gammaNativeFullFocus_congruence
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
    let e := gammaFullFocusIsoAt hκ hs h00 hr U h D hfull hAd hA hD
    let η := ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.last n) hAd)
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization U ω))
      (gammaGroundMeasuredRVSemiringClass (gammaNativeMeasuredNormalization V
        (η.comp (Section5.nativeRVGroundIso e).map))) := by
  have hS := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show (⟨Section5.nativeRVGroundObject U hweight,ω⟩ : GammaGroundMeasuredRVObject hc B (n+1)) ⟶
      gammaNativeMeasuredNormalization U ω from gammaNativeFullWeightNormalizationHom U hweight ω))
  have hE := gammaGroundMeasuredRVSemiringClass_iso (asIso
    (show gammaNativeMeasuredNormalization _ _ ⟶ gammaNativeMeasuredNormalization _ _ from
      gammaMeasuredFullFocusHom hκ hs h00 hr U h D hfull hAd hA hD ω))
  dsimp only
  rw [← hS,hE]
  exact gammaNativeElementary_principal_congruence hκ hs h00 hr U hweight ω hAd

end DiamondIntegral.Section3
