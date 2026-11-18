import «section 3».GammaNativeMeasuredLifts
import «section 3».GammaNativeUnitLiftBridge

/-! Arbitrary forms survive the literal conversion between the local and
native full-label RV presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeMeasuredLiftBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredRVObject hc B k) : GammaGroundMeasuredVFHom hκ hs hr hv
      (gammaNativeMeasuredLift (Section5.groundRVAt U.underlying)
        (U.form.comp (Section5.groundRVObjectRoundTrip U.underlying).map))
      (gammaGroundMeasuredObjectLift U) :=
  gammaMeasuredHomOfCarrierEq hκ hs hr hv rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq (Section5.groundRVAt_lift_domain U.underlying)))
    (fun p q hpq => by
      have he : p.val = q.val := eq_of_heq hpq
      change (gammaGroundFormValue U.form
        ((Section5.groundRVObjectRoundTrip U.underlying).map
          (gammaNativeLiftLabel (Section5.groundRVAt U.underlying) p))).val =
        (gammaGroundFormValue U.form (gammaGroundObjectLiftLabel U.underlying q)).val
      congr 2
      apply Subtype.ext
      exact congrArg Prod.snd he)

end DiamondIntegral.Section3
