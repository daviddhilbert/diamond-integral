import «section 3».GammaNativeElementaryChart
import «section 3».GammaNativeHeadFiniteness
import «section 3».GammaMeasuredElementaryForm
import «section 3».GammaNativeMeasuredNormalization

/-! The actual native elementary form lies in the original homogeneous
special congruence. Both its weight and its finite head are proved from
native admissibility. -/
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
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)

theorem gammaNativeElementary_weight (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (w : (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
      (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))).underlying.domain) :
    (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
      (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))).combinedWeight w =
      (⟨Section5.nativeRVGroundObject U hfull,ω⟩ : GammaGroundMeasuredRVObject hc B (n+1)).combinedWeight
        ⟨((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).val.1,
          ((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).property.1⟩ *
      (gammaGroundMeasuredRVPositive hc B).combinedWeight
        ⟨((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).val.2,
          ((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).property.2⟩ := by
  let V : GammaGroundMeasuredRVObject hc B (n+1) := ⟨Section5.nativeRVGroundObject U hfull,ω⟩
  let E := gammaElementaryAt hκ hs h00 hr U i hAd
  let W := gammaNativeMeasuredNormalization E (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd))
  let z := (gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w
  let u : V.underlying.domain := ⟨z.val.1,z.property.1⟩
  let t : (gammaGroundMeasuredRVPositive hc B).underlying.domain := ⟨z.val.2,z.property.2⟩
  have hf : gammaGroundFormValue W.form w = gammaGroundFormValue ω u := by
    change gammaGroundFormValue ω _ = gammaGroundFormValue ω u
    congr 1
    apply Subtype.ext
    exact (congrArg Prod.fst (gammaNativeElementaryChart_val hκ hs h00 hr U hfull i hAd w)).symm
  have hL : gammaGroundFormValue W.underlying.labelWeightForm w =
      gammaGroundFormValue V.underlying.labelWeightForm u * (gammaGroundMeasuredRVPositive hc B).combinedWeight t := by
    apply Subtype.ext
    rw [gammaGroundLabelWeight_val,Values.gamma_val_mul,gammaGroundLabelWeight_val]
    change (∏ j, Values.vrv ((Section5.nativeRVGroundVolume (gammaHighRestrictionAt E) w).val j)) =
      (∏ j, Values.vrv ((Section5.nativeRVGroundVolume U u).val j)) *
        ((gammaGroundMeasuredRVPositive hc B).combinedWeight t).val
    rw [gammaNativeElementaryChart_volume hκ hs h00 hr U hfull i hAd w,gammaRadiusProduct_blowup]
    have ht : ((gammaGroundMeasuredRVPositive hc B).combinedWeight t).val =
        Values.vrv ((show Fin 1 → CanonicalRV.RVSort M from t.val) 0) := by
      change ((1 : Values.Gamma (M := M)) * ∏ j : Fin 1, Section2.rvFiniteValue
        ((gammaGroundMeasuredRVPositive hc B).underlying.target t j)).val = _
      rw [one_mul,Fin.prod_univ_one,Section2.rvFiniteValue_val]
      rfl
    rw [ht]
    exact mul_comm _ _
  change W.combinedWeight w = V.combinedWeight u * (gammaGroundMeasuredRVPositive hc B).combinedWeight t
  calc
    _ = gammaGroundFormValue W.form w * gammaGroundFormValue W.underlying.labelWeightForm w := by
      rw [W.underlying.labelWeightForm_value]
      rfl
    _ = (gammaGroundFormValue ω u * gammaGroundFormValue V.underlying.labelWeightForm u) *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight t := by rw [hf,hL,mul_assoc]
    _ = _ := by rw [V.underlying.labelWeightForm_value]; rfl

theorem gammaNativeElementary_principal_congruence (U : GammaObjectAt B Set.univ (n+1))
    (hfull : GammaFullWeightAt U) (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last n)) :
    gammaGroundMeasuredRVSpecialCongruence hc B
      (gammaGroundMeasuredRVSemiringClass (⟨Section5.nativeRVGroundObject U hfull,ω⟩ : GammaGroundMeasuredRVObject hc B (n+1)))
      (gammaGroundMeasuredRVSemiringClass
        (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U (Fin.last n) hAd)
          (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U (Fin.last n) hAd)))) :=
  gammaMeasuredElementary_principal_congruence _ _
    (gammaNativeHead_finite_of_admissible hκ hs h00 hr U hfull hAd)
    (gammaNativeElementaryChart hκ hs h00 hr U hfull (Fin.last n) hAd)
    (gammaNativeElementary_weight hκ hs h00 hr U hfull ω (Fin.last n) hAd)

end DiamondIntegral.Section3
