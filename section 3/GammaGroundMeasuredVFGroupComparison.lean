import «section 3».CompletionDirectSum
import «section 3».GammaGroundMeasuredVFGradedSemiring

/-! The measured VF group grading is the direct sum of the actual
fixed-degree Grothendieck groups, relative to the accepted lift records. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}


def gammaGroundMeasuredVFGroupDirectSumEquiv (H : YinGammaGroundMeasuredLiftInput C hc hv) (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    GammaGroundMeasuredVFGrothendieckRing C hc hv ≃+
      DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k)) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact (gammaGroundMeasuredVFGradedRingEquiv H D).symm.toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv))

end DiamondIntegral.Section3
