import «section 3».GammaGroundMeasuredVFRelativeComparison
import «section 3».GammaGroundMeasuredRVQuotientGrading

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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}


def gammaGroundMeasuredVFPolynomialGrading (H : YinGammaGroundMeasuredLiftInput C hc hv) :
    GammaGroundMeasuredVFPositiveSemiring C hc hv →+* GammaGroundMeasuredRVGradingPolynomial hc C.base :=
  gammaGroundMeasuredRVQuotientGrading.comp (gammaGroundMeasuredPositiveIntegral H).toRingHom

theorem gammaGroundMeasuredVFPolynomialGrading_add (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (a b : GammaGroundMeasuredVFPositiveSemiring C hc hv) :
    gammaGroundMeasuredVFPolynomialGrading H (a + b) = gammaGroundMeasuredVFPolynomialGrading H a + gammaGroundMeasuredVFPolynomialGrading H b :=
  (gammaGroundMeasuredVFPolynomialGrading H).map_add' a b

theorem gammaGroundMeasuredPositiveIntegral_add (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (a b : GammaGroundMeasuredVFPositiveSemiring C hc hv) :
    gammaGroundMeasuredPositiveIntegral H (a + b) = gammaGroundMeasuredPositiveIntegral H a + gammaGroundMeasuredPositiveIntegral H b :=
  (gammaGroundMeasuredPositiveIntegral H).map_add' a b

theorem gammaGroundMeasuredVFPolynomialGrading_fixed (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} (a : GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) :
    gammaGroundMeasuredVFPolynomialGrading H (gammaGroundMeasuredVFKPlusToSemiring C hc hv a) =
      (Polynomial.monomial k (gammaGroundMeasuredPositiveIntegral H (gammaGroundMeasuredVFKPlusToSemiring C hc hv a)) :
        GammaGroundMeasuredRVGradingPolynomial hc C.base) := by
  obtain ⟨x, rfl⟩ := D.surjective k a
  have he := DFunLike.congr_fun (gammaGroundMeasuredLift_degree_compat H D k) x
  change H.lift (gammaGroundMeasuredRVKPlusToSemiring x) =
    gammaGroundMeasuredVFKPlusToSemiring C hc hv (D.lift k x) at he
  rw [← he]
  have hi : gammaGroundMeasuredPositiveIntegral H (H.lift (gammaGroundMeasuredRVKPlusToSemiring x)) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring x) := by
    exact (semiringIntegralFromKernel_characterization H.lift H.surjective _ H.kernel _ _).mpr rfl
  change gammaGroundMeasuredRVQuotientGrading (gammaGroundMeasuredPositiveIntegral H _) = _
  rw [hi]
  exact gammaGroundMeasuredRVQuotientGrading_fixed x

end DiamondIntegral.Section3
