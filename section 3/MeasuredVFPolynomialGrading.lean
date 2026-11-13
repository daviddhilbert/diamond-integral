import «section 3».MeasuredVFRelativeComparison
import «section 3».MeasuredRVQuotientGrading

/-! The accepted measured lift comparisons transport the checked degree
grading to actual VF classes, without identifying distinct degrees. -/
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

def measuredVFPolynomialGrading (H : YinMeasuredLiftInput C hc B) :
    MeasuredVFPositiveSemiring C hc →+* MeasuredRVGradingPolynomial hc (C.base : Set M) :=
  measuredRVQuotientGrading.comp (measuredPositiveIntegral H).toRingHom

theorem measuredVFPolynomialGrading_add (H : YinMeasuredLiftInput C hc B)
    (a b : MeasuredVFPositiveSemiring C hc) :
    measuredVFPolynomialGrading H (a + b) = measuredVFPolynomialGrading H a + measuredVFPolynomialGrading H b :=
  (measuredVFPolynomialGrading H).map_add' a b

theorem measuredPositiveIntegral_add (H : YinMeasuredLiftInput C hc B)
    (a b : MeasuredVFPositiveSemiring C hc) :
    measuredPositiveIntegral H (a + b) = measuredPositiveIntegral H a + measuredPositiveIntegral H b :=
  (measuredPositiveIntegral H).map_add' a b

theorem measuredVFPolynomialGrading_fixed (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) {k : ℕ} (a : MeasuredVFKPlus C hc k) :
    measuredVFPolynomialGrading H (measuredVFKPlusToSemiring C hc a) =
      (Polynomial.monomial k (measuredPositiveIntegral H (measuredVFKPlusToSemiring C hc a)) :
        MeasuredRVGradingPolynomial hc (C.base : Set M)) := by
  obtain ⟨x, rfl⟩ := D.surjective k a
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc x
  rw [D.lift_class, measuredVFKPlusToSemiring_class]
  have he := (measuredPositiveIntegral_characterization H (measuredObjectLift hc C k U) U).mpr rfl
  change measuredRVQuotientGrading (measuredPositiveIntegral H _) = _
  rw [he]
  exact measuredRVQuotientGrading_class U

end DiamondIntegral.Section3
