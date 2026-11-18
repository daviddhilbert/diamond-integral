import «section 3».GammaMeasuredElementaryValues

/-! The elementary weight is exactly the original form on the retained
label. The principal-congruence construction therefore introduces no
change of density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
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

theorem gammaGroundLabelWeight_val {k : ℕ} (U : GammaGroundRVObject hc B k) (u : U.domain) :
    (gammaGroundFormValue U.labelWeightForm u).val = ∏ j, Values.vrv ((U.volume u).val j) := by
  rw [U.labelWeightForm_value]
  change Values.gammaValHom (∏ j, Section2.rvFiniteValue (U.target u j)) = _
  rw [map_prod]
  rfl

theorem gammaMeasuredElementaryObject_form
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) :
    gammaGroundFormValue (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).form w =
      gammaGroundFormValue U.form
        ⟨((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.1,
          ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).property.1⟩ := by
  let W := gammaMeasuredElementaryObject hκ hs h00 hr U i hAd
  let z := (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w
  let u : U.underlying.domain := ⟨z.val.1,z.property.1⟩
  let t : (gammaGroundMeasuredRVPositive hc B).underlying.domain := ⟨z.val.2,z.property.2⟩
  have hL : gammaGroundFormValue W.underlying.labelWeightForm w =
      gammaGroundFormValue U.underlying.labelWeightForm u *
        (gammaGroundMeasuredRVPositive hc B).combinedWeight t := by
    apply Subtype.ext
    rw [gammaGroundLabelWeight_val,Values.gamma_val_mul,gammaGroundLabelWeight_val,
      gammaMeasuredElementaryObject_volume hκ hs h00 hr U i hAd w,gammaRadiusProduct_blowup]
    have ht : ((gammaGroundMeasuredRVPositive hc B).combinedWeight t).val = Values.vrv ((show Fin 1 → CanonicalRV.RVSort M from t.val) 0) := by
      change ((1 : Values.Gamma (M := M)) * ∏ j : Fin 1, Section2.rvFiniteValue
        ((gammaGroundMeasuredRVPositive hc B).underlying.target t j)).val = _
      rw [one_mul,Fin.prod_univ_one,Section2.rvFiniteValue_val]
      rfl
    rw [ht]
    exact mul_comm _ _
  have hW := gammaMeasuredElementaryObject_weight hκ hs h00 hr U i hAd w
  change gammaGroundFormValue W.form w = gammaGroundFormValue U.form u
  apply mul_right_cancel (b := gammaGroundFormValue W.underlying.labelWeightForm w)
  calc
    _ = W.combinedWeight w := by rw [W.underlying.labelWeightForm_value]; rfl
    _ = U.combinedWeight u * (gammaGroundMeasuredRVPositive hc B).combinedWeight t := hW
    _ = gammaGroundFormValue U.form u * gammaGroundFormValue W.underlying.labelWeightForm w := by
      rw [hL,U.underlying.labelWeightForm_value]
      exact mul_assoc _ _ _

end DiamondIntegral.Section3
