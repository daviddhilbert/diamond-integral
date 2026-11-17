import «section 3».GammaNativeLiftPermutations
import «section 3».GammaGroundVFPermutationJacobians
import «section 3».GammaFullMeasuredBijections

/-! The actual permutation of a native lift is Gamma measured for its
transported retained form. Its Jacobian is the permutation sign. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeLiftPermutationFullMeasured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaObjectAt B Set.univ (n+1)) (σ : Equiv.Perm (Fin (n+1)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω)
      (gammaNativeMeasuredLift (U.reindexVolume σ) (gammaNativePermutedForm U σ ω)) := by
  let E := gammaNativeLiftPermutation (hc := hc) U σ
  refine ⟨E,?_⟩
  intro p hp
  refine ⟨(Equiv.Perm.sign σ : Section2.VF M),?_,?_⟩
  · exact gammaGroundVFPermutation_jacobian hκ hs hr hv E.map σ (fun _ => rfl) p hp
  · rw [gammaVFPermutationSign_value,mul_one]
    change (cast (gammaCarrier hc) (ω (gammaNativeLiftLabel U p)).val).val =
      (cast (gammaCarrier hc) (gammaNativePermutedForm U σ ω
        (gammaNativeLiftLabel (U.reindexVolume σ) (E.map p))).val).val
    rw [gammaNativeLiftPermutation_label,gammaNativePermutedForm_value]

end DiamondIntegral.Section3
