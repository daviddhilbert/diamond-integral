import «section 3».GammaGroundMeasuredVFDirectSum
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}


def gammaGroundMeasuredVFDirectSumClass {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    GammaGroundMeasuredVFDirectSum C hc hv :=
  DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base)
    C.uncountable.le C.saturated C.small_real hv) k
    (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv U)

@[simp] theorem gammaGroundMeasuredVFDirectSumToSemiring_class {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    gammaGroundMeasuredVFDirectSumToSemiring (gammaGroundMeasuredVFDirectSumClass (hv := hv) U) = gammaGroundMeasuredVFSemiringClass C hc hv U :=
  (gammaGroundMeasuredVFDirectSumToSemiring_of k _).trans (gammaGroundMeasuredVFKPlusToSemiring_class C hc hv U)

@[instance_reducible]
def gammaGroundMeasuredVFDirectSumCommSemiring (H : YinGammaGroundMeasuredLiftInput C hc hv) (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    CommSemiring (GammaGroundMeasuredVFDirectSum C hc hv) := additiveTransportCommSemiring (gammaGroundMeasuredVFDirectSumEquiv H D)

def gammaGroundMeasuredVFGradedSemiringEquiv (H : YinGammaGroundMeasuredLiftInput C hc hv) (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    GammaGroundMeasuredVFDirectSum C hc hv ≃+* GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  additiveTransportRingEquiv (gammaGroundMeasuredVFDirectSumEquiv H D)

theorem gammaGroundMeasuredVFDirectSumClass_product (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k l : ℕ}
    (U : GammaGroundMeasuredVFData hc C.base k) (V : GammaGroundMeasuredVFData hc C.base l) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    gammaGroundMeasuredVFDirectSumClass (U.product V) = gammaGroundMeasuredVFDirectSumClass U * gammaGroundMeasuredVFDirectSumClass V := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  let e := gammaGroundMeasuredVFGradedSemiringEquiv H D
  apply e.injective
  have hU : e (gammaGroundMeasuredVFDirectSumClass U) = gammaGroundMeasuredVFSemiringClass C hc hv U :=
    gammaGroundMeasuredVFDirectSumToSemiring_class U
  have hV : e (gammaGroundMeasuredVFDirectSumClass V) = gammaGroundMeasuredVFSemiringClass C hc hv V :=
    gammaGroundMeasuredVFDirectSumToSemiring_class V
  calc
    _ = gammaGroundMeasuredVFSemiringClass C hc hv (U.product V) := gammaGroundMeasuredVFDirectSumToSemiring_class _
    _ = gammaGroundMeasuredVFSemiringClass C hc hv U * gammaGroundMeasuredVFSemiringClass C hc hv V :=
      gammaGroundMeasuredVFSemiringClass_product C hc hv U V
    _ = e (gammaGroundMeasuredVFDirectSumClass U) * e (gammaGroundMeasuredVFDirectSumClass V) := congrArg₂ (· * ·) hU.symm hV.symm
    _ = _ := (e.map_mul' _ _).symm

theorem gammaGroundMeasuredVFDirectSumClass_unit (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    gammaGroundMeasuredVFDirectSumClass (GammaGroundMeasuredVFData.unit hc C.base) = 1 := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  let e := gammaGroundMeasuredVFGradedSemiringEquiv H D
  apply e.injective
  calc
    _ = gammaGroundMeasuredVFSemiringClass C hc hv (GammaGroundMeasuredVFData.unit hc C.base) := gammaGroundMeasuredVFDirectSumToSemiring_class _
    _ = 1 := PositiveGrothendieck.of_unit (gammaGroundMeasuredVFSemiringPresentation C hc hv)
    _ = _ := e.map_one.symm

def gammaGroundMeasuredVFGradedRingEquiv (H : YinGammaGroundMeasuredLiftInput C hc hv) (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv) ≃+* GammaGroundMeasuredVFGrothendieckRing C hc hv := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact ringCompletionCongr (gammaGroundMeasuredVFGradedSemiringEquiv H D)

end DiamondIntegral.Section3
