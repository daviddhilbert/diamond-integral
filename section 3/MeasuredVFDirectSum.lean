import «section 3».MeasuredVFPolynomialGrading
import «section 3».MeasuredRVGradedComparison
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (VFType (M := M))]
variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : Section2.VFGeneratedFieldBase C.base}

abbrev MeasuredVFDirectSum (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  DirectSum ℕ (MeasuredVFKPlus C hc)

def measuredVFDirectSumToSemiring : MeasuredVFDirectSum C hc →+ MeasuredVFPositiveSemiring C hc :=
  DirectSum.toAddMonoid (fun _ => measuredVFKPlusToSemiring C hc)

@[simp] theorem measuredVFDirectSumToSemiring_of (k : ℕ) (a : MeasuredVFKPlus C hc k) :
    measuredVFDirectSumToSemiring (DirectSum.of (MeasuredVFKPlus C hc) k a) = measuredVFKPlusToSemiring C hc a :=
  DirectSum.toAddMonoid_of _ _ _

theorem measuredVFDirectSumToSemiring_add (a b : MeasuredVFDirectSum C hc) :
    measuredVFDirectSumToSemiring (a + b) = measuredVFDirectSumToSemiring a + measuredVFDirectSumToSemiring b :=
  measuredVFDirectSumToSemiring.map_add' a b

theorem measuredVFKPlusToSemiring_add {k : ℕ} (a b : MeasuredVFKPlus C hc k) :
    measuredVFKPlusToSemiring C hc (a + b) = measuredVFKPlusToSemiring C hc a + measuredVFKPlusToSemiring C hc b :=
  (measuredVFKPlusToSemiring C hc).map_add' a b

theorem measuredVFDirectSum_grading_coeff (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) (a : MeasuredVFDirectSum C hc) (k : ℕ) :
    (measuredVFPolynomialGrading H (measuredVFDirectSumToSemiring a)).coeff k =
      measuredPositiveIntegral H (measuredVFKPlusToSemiring C hc (a k)) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, Polynomial.coeff_zero, DFinsupp.zero_apply]
  | of i a =>
    rw [measuredVFDirectSumToSemiring_of, measuredVFPolynomialGrading_fixed H D]
    by_cases he : i = k
    · subst k
      rw [Polynomial.coeff_monomial_same, DirectSum.of_eq_same]
    · rw [Polynomial.coeff_monomial_of_ne _ (Ne.symm he), DirectSum.of_eq_of_ne _ _ _ (Ne.symm he),
        map_zero, map_zero]
  | add a b ha hb =>
    rw [measuredVFDirectSumToSemiring_add, measuredVFPolynomialGrading_add, Polynomial.coeff_add,
      DFinsupp.add_apply, measuredVFKPlusToSemiring_add, measuredPositiveIntegral_add, ha, hb]

theorem measuredVFDirectSumToSemiring_injective (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) :
    Function.Injective (measuredVFDirectSumToSemiring (C := C) (hc := hc)) := by
  intro a b h
  apply DirectSum.ext
  intro k
  apply measuredVFKPlusToSemiring_injective H D k
  apply (measuredPositiveIntegral H).injective
  have ht := congrArg (fun x : MeasuredVFPositiveSemiring C hc => (measuredVFPolynomialGrading H x).coeff k) h
  rw [measuredVFDirectSum_grading_coeff H D, measuredVFDirectSum_grading_coeff H D] at ht
  exact ht

def measuredRVToVFDirectSum (D : YinDegreeMeasuredLiftInput C hc B) :
    MeasuredRVDirectSum hc (C.base : Set M) →+ MeasuredVFDirectSum C hc :=
  DirectSum.map D.lift

theorem measuredVFDirectSum_lift_compat (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) (a : MeasuredRVDirectSum hc (C.base : Set M)) :
    measuredVFDirectSumToSemiring (measuredRVToVFDirectSum D a) =
      H.lift (measuredRVDirectSumToPresentation a) := by
  have he : measuredVFDirectSumToSemiring.comp (measuredRVToVFDirectSum D) =
      H.lift.toAddMonoidHom.comp measuredRVDirectSumToPresentation.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro k x
    change measuredVFDirectSumToSemiring (DirectSum.map D.lift
      (DirectSum.of (MeasuredRVKPlus hc (C.base : Set M)) k x)) = _
    rw [DirectSum.map_of, measuredVFDirectSumToSemiring_of]
    change _ = H.lift (measuredRVDirectSumToPresentationAdd (DirectSum.of _ k x))
    rw [measuredRVDirectSumToPresentationAdd_of]
    exact (congrArg (fun f : MeasuredRVKPlus hc (C.base : Set M) k →+ MeasuredVFPositiveSemiring C hc => f x)
      (measuredLift_degree_compat H D k)).symm
  exact congrArg (fun f : MeasuredRVDirectSum hc (C.base : Set M) →+ MeasuredVFPositiveSemiring C hc => f a) he

theorem measuredVFDirectSumToSemiring_surjective (H : YinMeasuredLiftInput C hc B)
    (D : YinDegreeMeasuredLiftInput C hc B) :
    Function.Surjective (measuredVFDirectSumToSemiring (C := C) (hc := hc)) := by
  intro a
  obtain ⟨x, rfl⟩ := H.surjective a
  refine ⟨measuredRVToVFDirectSum D (measuredRVPresentationToDirectSum x), ?_⟩
  rw [measuredVFDirectSum_lift_compat H D]
  have he : measuredRVDirectSumToPresentation (measuredRVPresentationToDirectSum x) = x :=
    (measuredRVSemiringEquivDirectSum (hc := hc) (S := (C.base : Set M))).symm_apply_apply x
  rw [he]

def measuredVFDirectSumEquiv (H : YinMeasuredLiftInput C hc B) (D : YinDegreeMeasuredLiftInput C hc B) :
    MeasuredVFDirectSum C hc ≃+ MeasuredVFPositiveSemiring C hc :=
  AddEquiv.ofBijective measuredVFDirectSumToSemiring
    ⟨measuredVFDirectSumToSemiring_injective H D, measuredVFDirectSumToSemiring_surjective H D⟩

end DiamondIntegral.Section3
