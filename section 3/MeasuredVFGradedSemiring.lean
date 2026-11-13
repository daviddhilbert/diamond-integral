import «section 3».MeasuredVFDirectSum
import «section 3».AdditiveSemiringTransport
import «section 3».CompletionEquivalences

/-! The actual measured VF direct sum carries the cartesian-product
semiring, relative to the explicit accepted lift inputs. -/
set_option backward.isDefEq.respectTransparency false
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

def measuredVFDirectSumClass {k : ℕ} (U : MeasuredVFData C hc k) : MeasuredVFDirectSum C hc :=
  DirectSum.of (MeasuredVFKPlus C hc) k (measuredVFDataClass U)

@[simp] theorem measuredVFDirectSumToSemiring_class {k : ℕ} (U : MeasuredVFData C hc k) :
    measuredVFDirectSumToSemiring (measuredVFDirectSumClass U) = measuredVFDataSemiringClass C hc U :=
  (measuredVFDirectSumToSemiring_of k (measuredVFDataClass U)).trans (measuredVFDataClass_inclusion U)

@[instance_reducible]
def measuredVFDirectSumCommSemiring (H : YinMeasuredLiftInput C hc B) (D : YinDegreeMeasuredLiftInput C hc B) :
    CommSemiring (MeasuredVFDirectSum C hc) := additiveTransportCommSemiring (measuredVFDirectSumEquiv H D)

def measuredVFGradedSemiringEquiv (H : YinMeasuredLiftInput C hc B) (D : YinDegreeMeasuredLiftInput C hc B) :
    letI := measuredVFDirectSumCommSemiring H D
    MeasuredVFDirectSum C hc ≃+* MeasuredVFPositiveSemiring C hc :=
  additiveTransportRingEquiv (measuredVFDirectSumEquiv H D)

theorem measuredVFDirectSumClass_product (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) {k l : ℕ}
    (U : MeasuredVFData C hc k) (V : MeasuredVFData C hc l) :
    letI := measuredVFDirectSumCommSemiring H D
    measuredVFDirectSumClass (U.product V) = measuredVFDirectSumClass U * measuredVFDirectSumClass V := by
  letI := measuredVFDirectSumCommSemiring H D
  let e := measuredVFGradedSemiringEquiv H D
  apply e.injective
  have hU : e (measuredVFDirectSumClass U) = measuredVFDataSemiringClass C hc U :=
    measuredVFDirectSumToSemiring_class U
  have hV : e (measuredVFDirectSumClass V) = measuredVFDataSemiringClass C hc V :=
    measuredVFDirectSumToSemiring_class V
  calc
    _ = measuredVFDataSemiringClass C hc (U.product V) := measuredVFDirectSumToSemiring_class _
    _ = measuredVFDataSemiringClass C hc U * measuredVFDataSemiringClass C hc V :=
      measuredVFDataSemiringClass_product C hc U V
    _ = e (measuredVFDirectSumClass U) * e (measuredVFDirectSumClass V) := congrArg₂ (· * ·) hU.symm hV.symm
    _ = _ := (e.map_mul' _ _).symm

theorem measuredVFDirectSumClass_unit (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) :
    letI := measuredVFDirectSumCommSemiring H D
    measuredVFDirectSumClass (MeasuredVFData.unit C hc) = 1 := by
  letI := measuredVFDirectSumCommSemiring H D
  let e := measuredVFGradedSemiringEquiv H D
  apply e.injective
  calc
    _ = measuredVFDataSemiringClass C hc (MeasuredVFData.unit C hc) := measuredVFDirectSumToSemiring_class _
    _ = 1 := PositiveGrothendieck.of_unit (measuredVFSemiringPresentation C hc)
    _ = _ := e.map_one.symm

def measuredVFGradedRingEquiv (H : YinMeasuredLiftInput C hc B) (D : YinDegreeMeasuredLiftInput C hc B) :
    letI := measuredVFDirectSumCommSemiring H D
    RingCompletion (MeasuredVFDirectSum C hc) ≃+* MeasuredVFGrothendieckRing C hc := by
  letI := measuredVFDirectSumCommSemiring H D
  exact ringCompletionCongr (measuredVFGradedSemiringEquiv H D)

end DiamondIntegral.Section3
