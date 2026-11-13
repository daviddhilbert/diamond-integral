import «section 3».GammaGroundMeasuredVFPolynomialGrading
import «section 3».PresentationAdditiveNormalForm
import Mathlib.Algebra.Polynomial.Coeff

/-! Measured VF positive classes decompose uniquely by degree, relative
to the explicit accepted global and degreewise lift comparisons. -/
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


abbrev GammaGroundMeasuredVFDirectSum (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :=
  DirectSum ℕ (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv)

def gammaGroundMeasuredVFDirectSumToSemiring : GammaGroundMeasuredVFDirectSum C hc hv →+ GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  DirectSum.toAddMonoid (fun _ => gammaGroundMeasuredVFKPlusToSemiring C hc hv)

@[simp] theorem gammaGroundMeasuredVFDirectSumToSemiring_of (k : ℕ) (a : GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) :
    gammaGroundMeasuredVFDirectSumToSemiring (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv) k a) = gammaGroundMeasuredVFKPlusToSemiring C hc hv a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundMeasuredVFDirectSumToSemiring_add (a b : GammaGroundMeasuredVFDirectSum C hc hv) :
    gammaGroundMeasuredVFDirectSumToSemiring (a + b) = gammaGroundMeasuredVFDirectSumToSemiring a + gammaGroundMeasuredVFDirectSumToSemiring b :=
  gammaGroundMeasuredVFDirectSumToSemiring.map_add' a b

theorem gammaGroundMeasuredVFKPlusToSemiring_add {k : ℕ} (a b : GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) :
    gammaGroundMeasuredVFKPlusToSemiring C hc hv (a + b) = gammaGroundMeasuredVFKPlusToSemiring C hc hv a + gammaGroundMeasuredVFKPlusToSemiring C hc hv b :=
  (gammaGroundMeasuredVFKPlusToSemiring C hc hv).map_add' a b

theorem gammaGroundMeasuredVFDirectSum_grading_coeff (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (a : GammaGroundMeasuredVFDirectSum C hc hv) (k : ℕ) :
    (gammaGroundMeasuredVFPolynomialGrading H (gammaGroundMeasuredVFDirectSumToSemiring a)).coeff k =
      gammaGroundMeasuredPositiveIntegral H (gammaGroundMeasuredVFKPlusToSemiring C hc hv (a k)) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, Polynomial.coeff_zero, DFinsupp.zero_apply]
  | of i a =>
    rw [gammaGroundMeasuredVFDirectSumToSemiring_of, gammaGroundMeasuredVFPolynomialGrading_fixed H D]
    by_cases he : i = k
    · subst k
      rw [Polynomial.coeff_monomial_same, DirectSum.of_eq_same]
    · rw [Polynomial.coeff_monomial_of_ne _ (Ne.symm he), DirectSum.of_eq_of_ne _ _ _ (Ne.symm he),
        map_zero, map_zero]
  | add a b ha hb =>
    rw [gammaGroundMeasuredVFDirectSumToSemiring_add, gammaGroundMeasuredVFPolynomialGrading_add, Polynomial.coeff_add,
      DFinsupp.add_apply, gammaGroundMeasuredVFKPlusToSemiring_add, gammaGroundMeasuredPositiveIntegral_add, ha, hb]

theorem gammaGroundMeasuredVFDirectSumToSemiring_injective (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    Function.Injective (gammaGroundMeasuredVFDirectSumToSemiring (C := C) (hc := hc) (hv := hv)) := by
  intro a b h
  apply DirectSum.ext
  intro k
  apply gammaGroundMeasuredVFKPlusToSemiring_injective H D k
  apply (gammaGroundMeasuredPositiveIntegral H).injective
  have ht := congrArg (fun x : GammaGroundMeasuredVFPositiveSemiring C hc hv => (gammaGroundMeasuredVFPolynomialGrading H x).coeff k) h
  rw [gammaGroundMeasuredVFDirectSum_grading_coeff H D, gammaGroundMeasuredVFDirectSum_grading_coeff H D] at ht
  exact ht

theorem gammaGroundMeasuredVFDirectSumToSemiring_surjective :
    Function.Surjective (gammaGroundMeasuredVFDirectSumToSemiring (C := C) (hc := hc) (hv := hv)) := by
  apply positivePresentation_additive_surjective (gammaGroundMeasuredVFSemiringPresentation C hc hv)
  rintro ⟨k, U⟩
  refine ⟨DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base)
    C.uncountable.le C.saturated C.small_real hv) k
      (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv U), ?_⟩
  rw [gammaGroundMeasuredVFDirectSumToSemiring_of, gammaGroundMeasuredVFKPlusToSemiring_class]
  rfl

def gammaGroundMeasuredVFDirectSumEquiv (H : YinGammaGroundMeasuredLiftInput C hc hv) (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    GammaGroundMeasuredVFDirectSum C hc hv ≃+ GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  AddEquiv.ofBijective gammaGroundMeasuredVFDirectSumToSemiring
    ⟨gammaGroundMeasuredVFDirectSumToSemiring_injective H D, gammaGroundMeasuredVFDirectSumToSemiring_surjective⟩

end DiamondIntegral.Section3
