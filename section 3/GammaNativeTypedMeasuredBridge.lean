import «section 3».GammaFullMeasuredFixedMaps
import «section 3».GammaNativeMeasuredLifts
import IntegrationSection6.NormalizedLifts

/-! The typed mixed presentation of a native measured lift is an actual
full measured comparison fixing every coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeTypedLift_definable (U : GammaObjectAt B Set.univ n) :
    GammaSetDefinable B (carrier (typedLift U.object.obj)) := by
  rw [typedLift_carrier]
  exact U.toGamma.lift_definable

def gammaNativeTypedLiftBijection (U : GammaObjectAt B Set.univ n) :
    GammaGroundBijection (Section5.nativeGammaPointDomain (hc := hc) (carrier (typedLift U.object.obj))
      (gammaNativeTypedLift_definable U)) (gammaNativeUnitLift (hc := hc) U.toGamma).domain :=
  GammaGroundBijection.ofCarrierEq (typedLift_carrier U.object.obj)

def gammaNativeTypedMeasuredData (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) : GammaGroundMeasuredVFData hc B n where
  arity := rvObjectArity U.object.obj
  domain := Section5.nativeGammaPointDomain (carrier (typedLift U.object.obj)) (gammaNativeTypedLift_definable U)
  finite := by
    intro x
    change {t : Fin (rvObjectArity U.object.obj) → CanonicalRV.RVSort M | (x,t) ∈ carrier (typedLift U.object.obj)}.Finite
    rw [typedLift_carrier]
    exact (gammaNativeUnitLift (hc := hc) U.toGamma).finite x
  form := (gammaNativeMeasuredLift U ω).form.comp (gammaNativeTypedLiftBijection U).map

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeTypedFullMeasured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaFullMeasuredBijection (gammaNativeTypedMeasuredData U ω) (gammaNativeMeasuredLift U ω) :=
  gammaFullMeasuredFixedVF hκ hs hr hv (gammaNativeTypedLiftBijection U) (fun _ => rfl) (fun _ => rfl)

end DiamondIntegral.Section3
