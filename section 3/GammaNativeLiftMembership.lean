import «section 3».GammaNativeMeasuredLifts
import «section 3».GammaNativeStructuralValues
import «section 5».Completed18LocalLift

/-! Membership in the native full lift is the literal structural volume
relation, including zero strata. No full-weight restriction is imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeLift_membership (U : GammaObjectAt B Set.univ n)
    (q : Section2.Mixed M n (rvObjectArity U.object.obj)) :
    q ∈ (gammaNativeUnitLift (hc := hc) U.toGamma).domain.carrier ↔
      ∃ u : Section5.nativeRVGroundDomain (hc := hc) U, u.val = q.2 ∧
        (Section5.nativeRVGroundVolume U u).val = Section2.tupleRV M q.1 := by
  change (∃ u : rvObjectDomain U.object.obj,u.val=q.2 ∧
    (rvObjectVolume U.object.obj u).val=@SpecialTransformations.Section4.tupleRV M N hN n q.1) ↔ _
  rw [Section5.completed18_tupleRV]
  constructor
  · rintro ⟨u,hu,hv⟩
    let w := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm u
    exact ⟨w,hu,(gammaNativeRVGroundVolume_value U w).trans hv⟩
  · rintro ⟨w,hw,hv⟩
    let u := Section5.nativeRVGroundDomainEquiv U w
    exact ⟨u,hw,(gammaNativeRVGroundVolume_value U w).symm.trans hv⟩

end DiamondIntegral.Section3
