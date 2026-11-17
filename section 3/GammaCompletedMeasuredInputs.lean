import «section 3».GammaCompletedSemiringDetector
import «section 3».GammaMeasuredQuotientLift

/-! Both complete Gamma-ground measured input records are constructed
from the proved lift, its surjectivity, and its exact semiring and
degreewise kernels. All mathematical base hypotheses remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaContextMeasuredSemiringLift_kernel :
    gammaGroundMeasuredRVSpecialCongruence hc C.base = RingCon.ker (gammaContextMeasuredSemiringLift C hc hv) := by
  apply le_antisymm (gammaMeasuredSpecialCongruence_le_lift_kernel C hc hv)
  intro a b h
  apply (gammaGroundMeasuredRVSpecialCongruence hc C.base).eq.mp
  have hComp := gammaCompletedSemiringDetector_lift C hc hv
  have hA := RingHom.congr_fun hComp a
  have hB := RingHom.congr_fun hComp b
  exact hA.symm.trans ((congrArg (gammaCompletedSemiringDetector C hc hv) h).trans hB)

def completedGammaGroundMeasuredLiftInput : YinGammaGroundMeasuredLiftInput C hc hv where
  lift := gammaContextMeasuredSemiringLift C hc hv
  lift_class := gammaContextMeasuredSemiringLift_class C hc hv
  surjective := gammaContextMeasuredSemiringLift_surjective C hc hv
  kernel := gammaContextMeasuredSemiringLift_kernel C hc hv

end DiamondIntegral.Section3
