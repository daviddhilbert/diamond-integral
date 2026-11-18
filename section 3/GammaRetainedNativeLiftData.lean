import «section 3».GammaRetainedNativeMeasuredPresentations
import «section 3».GammaNativeLiftMembership

/-! Native measured lifts are literal retained-density objects and
RV pullbacks, including the structural zero strata. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaRetainedNativeLiftData (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaRetainedMeasuredVFData hc B (n+1) where
  arity := rvObjectArity U.object.obj
  domain := (gammaNativeMeasuredLift U ω).domain
  finite := (gammaNativeMeasuredLift U ω).finite
  labels := Section5.nativeRVGroundDomain U
  labels_mem p := (gammaNativeLiftLabel U p).property
  form := ω

theorem gammaRetainedNativeLiftData_toMeasured (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    (gammaRetainedNativeLiftData U ω).toMeasured = gammaNativeMeasuredLift U ω := rfl

theorem gammaNativeLift_isRVPullback (U : GammaObjectAt B Set.univ (n+1)) :
    IsRVPullback (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier := by
  apply (isRVPullback_iff _).mpr
  intro p hp q hpq
  obtain ⟨u,hu,hv⟩ := (gammaNativeLift_membership U p).mp hp
  obtain ⟨hRV,hLabel⟩ := (sameRV_iff _ _).mp hpq
  apply (gammaNativeLift_membership U q).mpr
  refine ⟨u,hu.trans hLabel, hv.trans ?_⟩
  funext i
  apply Subtype.ext
  exact congrArg Subtype.val (hRV i)

end DiamondIntegral.Section3
