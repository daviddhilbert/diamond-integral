import «section 3».GammaLiftProductGeometry

/-! The actual Gamma-valued object lift commutes with cartesian
products, with exactly the original forms in every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def gammaMeasuredLiftProductHom
    (U : GammaGroundMeasuredRVObject hc B n) (V : GammaGroundMeasuredRVObject hc B m) :
    GammaGroundMeasuredVFHom hκ hs hr hv (gammaGroundMeasuredObjectLift (U.product V))
      ((gammaGroundMeasuredObjectLift U).product (gammaGroundMeasuredObjectLift V)) := by
  apply gammaMeasuredHomOfCarrierEq hκ hs hr hv
    (U := gammaGroundMeasuredObjectLift (U.product V))
    (V := (gammaGroundMeasuredObjectLift U).product (gammaGroundMeasuredObjectLift V)) rfl
  · exact heq_of_eq (gammaDefSet_eq_of_carrierEq (gammaObjectLift_product_carrier U.underlying V.underlying))
  · intro p q hpq
    have he : p.val = q.val := eq_of_heq hpq
    let a := gammaGroundObjectLiftLabel (U.product V).underlying p
    let b := gammaGroundMeasuredVFProductLeft (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V) q
    let c := gammaGroundMeasuredVFProductRight (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V) q
    have hR := gammaRVUnpack_value U.underlying.domain V.underlying.domain a
    have hM := gammaMixedUnpack_value (gammaGroundObjectLift U.underlying) (gammaGroundObjectLift V.underlying) q
    have hL : gammaGroundMeasuredRVProductLeft U V a = gammaGroundObjectLiftLabel U.underlying b := by
      apply Subtype.ext
      have h₁ := congrArg Prod.fst hR
      have h₂ := congrArg (fun z => z.1.2) hM
      exact h₁.trans ((congrArg (fun z => z.2 ∘ Fin.castAdd V.underlying.arity) he).trans h₂.symm)
    have hQ : gammaGroundMeasuredRVProductRight U V a = gammaGroundObjectLiftLabel V.underlying c := by
      apply Subtype.ext
      have h₁ := congrArg Prod.snd hR
      have h₂ := congrArg (fun z => z.2.2) hM
      exact h₁.trans ((congrArg (fun z => z.2 ∘ Fin.natAdd U.underlying.arity) he).trans h₂.symm)
    change (gammaGroundFormValue (U.product V).form a).val =
      (gammaGroundFormValue ((gammaGroundMeasuredObjectLift U).product (gammaGroundMeasuredObjectLift V)).form q).val
    rw [GammaGroundMeasuredRVObject.product_form,GammaGroundMeasuredVFData.product_form]
    change ((gammaGroundFormValue U.form _)*(gammaGroundFormValue V.form _)).val =
      ((gammaGroundFormValue U.form (gammaGroundObjectLiftLabel U.underlying b))*
        (gammaGroundFormValue V.form (gammaGroundObjectLiftLabel V.underlying c))).val
    rw [hL,hQ]

end DiamondIntegral.Section3
