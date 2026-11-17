import «section 3».MeasuredRealGroundRVInputs
import «section 3».MeasuredRealGroundVFCompatibility
import «section 3».MeasuredLifting

/-! The real/redundant-Gamma adapters commute with the literal measured
object lift. Identity-carrier arrows preserve the entire density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def liftFromRealHom {k : ℕ} (U : MeasuredRVObject (M := M) (C.base : Set M) k) :
    GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small hv
      (vfFromReal C hc B (MeasuredVFData.ofObject (measuredObjectLift hc C k U)))
      (gammaGroundMeasuredObjectLift (rvFromReal C hc B U)) := by
  cases k <;> apply gammaMeasuredHomOfCarrierEq C.uncountable.le C.saturated C.small hv rfl
  all_goals
    first
    | exact heq_of_eq (gammaDefSet_eq_of_carrierEq rfl)
    | intro p q hpq
      have he : p = q := Subtype.ext (eq_of_heq hpq)
      exact congrArg _ he

end DiamondIntegral.Section3.MeasuredRealGround
