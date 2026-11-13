import «section 3».CompletionDirectSum
import «section 3».MeasuredVFGradedSemiring

/-! The measured VF group grading is the direct sum of the actual
fixed-degree Grothendieck groups, relative to the accepted lift records. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (VFType (M := M))]
variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : Section2.VFGeneratedFieldBase C.base}

def measuredVFGroupDirectSumEquiv (H : YinMeasuredLiftInput C hc B) (D : YinDegreeMeasuredLiftInput C hc B) :
    MeasuredVFGrothendieckRing C hc ≃+
      DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (MeasuredVFKPlus C hc k)) := by
  letI := measuredVFDirectSumCommSemiring H D
  exact (measuredVFGradedRingEquiv H D).symm.toAddEquiv.trans
    (completionDirectSumEquiv (MeasuredVFKPlus C hc))

end DiamondIntegral.Section3
