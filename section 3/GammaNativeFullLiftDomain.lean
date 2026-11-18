import «section 3».GammaNativeStructuralValues
import «section 5».Completed18LocalLift

/-! A full-weight native object has exactly its literal local Gamma lift,
including its retained RV labels. -/
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
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeFullLift_carrier (U : GammaObjectAt B Set.univ n) (hfull : GammaFullWeightAt U) :
    U.toGamma.lift = (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) U hfull)).carrier := by
  let W := Section5.nativeRVGroundObject (hc := hc) U hfull
  ext q
  change (∃ u : rvObjectDomain U.object.obj,u.val=q.2 ∧
    (rvObjectVolume U.object.obj u).val=@SpecialTransformations.Section4.tupleRV M N hN n q.1) ↔ _
  rw [Section5.completed18_tupleRV]
  constructor
  · rintro ⟨u,hu,hv⟩
    let w := (Section5.nativeRVGroundDomainEquiv (hc := hc) U).symm u
    refine ⟨w,hu,?_⟩
    exact (gammaNativeRVGroundVolume_value U w).trans hv
  · rintro ⟨w,hw,hv⟩
    let u := Section5.nativeRVGroundDomainEquiv U w
    refine ⟨u,hw,?_⟩
    exact (gammaNativeRVGroundVolume_value U w).symm.trans hv

def gammaNativeFullLiftBijection (U : GammaObjectAt B Set.univ n) (hfull : GammaFullWeightAt U) :
    GammaGroundBijection (gammaNativeUnitLift (hc := hc) U.toGamma).domain
      (gammaGroundObjectLift (Section5.nativeRVGroundObject (hc := hc) U hfull)) :=
  GammaGroundBijection.ofCarrierEq (gammaNativeFullLift_carrier U hfull)

end DiamondIntegral.Section3
