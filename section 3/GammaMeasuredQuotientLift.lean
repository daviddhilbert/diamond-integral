import «section 3».GammaMeasuredBasicLiftRelation
import «section 3».GammaMeasuredSemiringLift
import «section 3».GammaGroundMeasuredRVGenerators

/-! The actual Gamma-valued lift factors through the originally stated
homogeneous special congruence. The resulting quotient lift is surjective;
its injectivity is the remaining kernel direction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaMeasuredSpecialCongruence_le_lift_kernel :
    gammaGroundMeasuredRVSpecialCongruence hc C.base ≤ RingCon.ker (gammaContextMeasuredSemiringLift C hc hv) := by
  apply RingCon.ringConGen_le.mpr
  rintro x y ⟨rfl,rfl⟩
  change gammaContextMeasuredSemiringLift C hc hv _ = gammaContextMeasuredSemiringLift C hc hv _
  rw [gammaContextMeasuredSemiringLift_class,gammaContextMeasuredSemiringLift_class]
  have h := congrArg (gammaGroundMeasuredVFKPlusToSemiring C hc hv (k := 1))
    (gammaMeasuredBasic_lift_class (hc := hc) (B := C.base) C.uncountable C.saturated C.model00 C.small_real C.small_gamma
      (C.fieldBase.gamma_closure_generated C.base.gamma) hv)
  simpa only [gammaGroundMeasuredVFKPlusToSemiring_class] using h

def gammaContextMeasuredQuotientLift : (gammaGroundMeasuredRVSpecialCongruence hc C.base).Quotient →+*
    GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  (gammaGroundMeasuredRVSpecialCongruence hc C.base).lift (gammaContextMeasuredSemiringLift C hc hv)
    (gammaMeasuredSpecialCongruence_le_lift_kernel C hc hv)

@[simp] theorem gammaContextMeasuredQuotientLift_mk (x : GammaGroundMeasuredRVPositiveSemiring hc C.base) :
    gammaContextMeasuredQuotientLift C hc hv ((gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' x) =
      gammaContextMeasuredSemiringLift C hc hv x := rfl

theorem gammaContextMeasuredQuotientLift_surjective :
    Function.Surjective (gammaContextMeasuredQuotientLift C hc hv) := by
  intro a
  obtain ⟨u,hu⟩ := gammaContextMeasuredSemiringLift_surjective C hc hv a
  exact ⟨(gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' u,hu⟩

end DiamondIntegral.Section3
