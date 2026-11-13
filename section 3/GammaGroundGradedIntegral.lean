import «section 3».GammaGroundMeasuredVFGroupComparison
import «section 3».GammaGroundVFSemiringColimit

/-! Accepted [18] integral comparisons on the actual VF graded and
filtered presentations over the full Gamma ground. Every cited lift
record remains an explicit argument. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

def gammaGroundMeasuredGradedIntegral (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    GammaGroundMeasuredVFDirectSum C hc hv ≃+* GammaGroundMeasuredRVSpecialQuotient hc C.base := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact (gammaGroundMeasuredVFGradedSemiringEquiv H D).trans (gammaGroundMeasuredPositiveIntegral H)

theorem gammaGroundMeasuredGradedIntegral_class (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc C.base k) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    gammaGroundMeasuredGradedIntegral H D (gammaGroundMeasuredVFDirectSumClass (gammaGroundMeasuredObjectLift U)) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVSemiringClass U) := by
  change gammaGroundMeasuredPositiveIntegral H
    (gammaGroundMeasuredVFDirectSumToSemiring (gammaGroundMeasuredVFDirectSumClass (gammaGroundMeasuredObjectLift U))) = _
  rw [gammaGroundMeasuredVFDirectSumToSemiring_class, gammaGroundMeasuredPositiveIntegral_lift_class]

def gammaGroundMeasuredGradedRingIntegral (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv) ≃+*
      GammaGroundMeasuredRVGrothendieckRing hc C.base ⧸ Ideal.span
        ({gammaGroundMeasuredRVPrincipalElement hc C.base} : Set (GammaGroundMeasuredRVGrothendieckRing hc C.base)) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact (gammaGroundMeasuredVFGradedRingEquiv H D).trans (gammaGroundMeasuredRingIntegral H)

def gammaGroundUnmeasuredFilteredIntegral (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    letI := gammaGroundFiniteVFCommSemiring H D
    GammaGroundFiniteVFKPlus hc C.base ≃+* (gammaGroundRVSpecialCongruence hc C.base).Quotient := by
  letI := gammaGroundFiniteVFCommSemiring H D
  exact (gammaGroundFiniteVFSemiringEquiv H D).trans (gammaGroundUnmeasuredPositiveIntegral H)

theorem gammaGroundUnmeasuredFilteredIntegral_class (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) {k : ℕ}
    (U : GammaGroundRVObject hc C.base k) :
    letI := gammaGroundFiniteVFCommSemiring H D
    gammaGroundUnmeasuredFilteredIntegral H D (gammaGroundFiniteVFClass (gammaGroundObjectLiftFinite U)) =
      (gammaGroundRVSpecialCongruence hc C.base).mk' (gammaGroundRVSemiringClass U) := by
  change gammaGroundUnmeasuredPositiveIntegral H (gammaGroundFiniteVFKPlusToSemiring
    (gammaGroundFiniteVFClass (gammaGroundObjectLiftFinite U))) = _
  rw [gammaGroundFiniteVFKPlusToSemiring_class, gammaGroundUnmeasuredPositiveIntegral_lift_class]

end DiamondIntegral.Section3
