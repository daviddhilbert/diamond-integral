import «section 3».MeasuredRVGenerators
import «section 3».MeasuredRVRepresentatives
import Mathlib.Algebra.Polynomial.Basic

/-! The measured elementary relation preserves degree. Recording the
degree by a polynomial variable descends to the actual special quotient. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

abbrev MeasuredRVSpecialQuotient (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  (measuredRVSpecialCongruence (M := M) hc S).Quotient

local instance measuredRVGradingCoefficientSemiring : Semiring (MeasuredRVSpecialQuotient hc S) :=
  (inferInstance : CommSemiring (MeasuredRVSpecialQuotient hc S)).toSemiring

abbrev MeasuredRVGradingPolynomial (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Polynomial (MeasuredRVSpecialQuotient hc S)

theorem measuredRVSpecialMap_zero :
    (measuredRVSpecialCongruence hc S).mk' 0 = (0 : MeasuredRVSpecialQuotient hc S) := rfl

theorem measuredRVSpecialMap_one :
    (measuredRVSpecialCongruence hc S).mk' 1 = (1 : MeasuredRVSpecialQuotient hc S) := rfl

theorem measuredRVSpecialMap_add (a b : MeasuredRVPositiveSemiring hc S) :
    (measuredRVSpecialCongruence hc S).mk' (a + b) =
      (measuredRVSpecialCongruence hc S).mk' a + (measuredRVSpecialCongruence hc S).mk' b := rfl

theorem measuredRVSpecialMap_mul (a b : MeasuredRVPositiveSemiring hc S) :
    (measuredRVSpecialCongruence hc S).mk' (a * b) =
      (measuredRVSpecialCongruence hc S).mk' a * (measuredRVSpecialCongruence hc S).mk' b := rfl

theorem measuredRVMonomial_add (k : ℕ) (a b : MeasuredRVSpecialQuotient hc S) :
    (Polynomial.monomial k (a + b) : MeasuredRVGradingPolynomial hc S) =
      Polynomial.monomial k a + Polynomial.monomial k b :=
  (Polynomial.monomial k).map_add' a b

def measuredRVPolynomialInvariant : PositiveGrothendieck.Invariant (measuredRVSemiringPresentation hc S)
    (R := MeasuredRVGradingPolynomial hc S) where
  toFun A := Polynomial.monomial A.1
    ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc A.2))
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (fun x => Polynomial.monomial k ((measuredRVSpecialCongruence hc S).mk' x))
      (measuredRVSemiringClass_iso hc e)
  empty := by
    change Polynomial.monomial 0 ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc (MeasuredRVObject.empty S 0))) = 0
    rw [measuredRVSemiringClass_empty, measuredRVSpecialMap_zero, Polynomial.monomial_zero_right]
  unit := by
    change Polynomial.monomial 0 ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc (MeasuredRVObject.unit hc S))) = 1
    rw [measuredRVSemiringClass_unit, measuredRVSpecialMap_one]
    exact Polynomial.monomial_zero_one
  product A B := by
    change Polynomial.monomial (A.1 + B.1) ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc (A.2.product hc B.2))) = _
    rw [measuredRVSemiringClass_product, measuredRVSpecialMap_mul, Polynomial.monomial_mul_monomial]
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hq := congrArg (measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass_scissor hc hs)
      rw [measuredRVSpecialMap_add, measuredRVSpecialMap_add] at hq
      have ht := congrArg (fun q : MeasuredRVSpecialQuotient hc S =>
        (Polynomial.monomial k q : MeasuredRVGradingPolynomial hc S)) hq
      rw [measuredRVMonomial_add, measuredRVMonomial_add] at ht
      exact ht
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [measuredRVSemiringClass_empty, measuredRVSpecialMap_zero, Polynomial.monomial_zero_right, add_zero]

def measuredRVPolynomialMap : MeasuredRVPositiveSemiring hc S →+* MeasuredRVGradingPolynomial hc S :=
  PositiveGrothendieck.lift (measuredRVSemiringPresentation hc S) measuredRVPolynomialInvariant

@[simp] theorem measuredRVPolynomialMap_class {k : ℕ} (U : MeasuredRVObject (M := M) S k) :
    measuredRVPolynomialMap (measuredRVSemiringClass hc U) =
      Polynomial.monomial k ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc U)) :=
  PositiveGrothendieck.lift_of (measuredRVSemiringPresentation hc S) measuredRVPolynomialInvariant ⟨k, U⟩

theorem measuredRVPolynomialMap_respects :
    measuredRVSpecialCongruence hc S ≤ RingCon.ker (measuredRVPolynomialMap (hc := hc) (S := S)) := by
  apply RingCon.ringConGen_le.mpr
  rintro x y ⟨rfl, rfl⟩
  change measuredRVPolynomialMap _ = measuredRVPolynomialMap _
  rw [measuredRVPolynomialMap_class, measuredRVPolynomialMap_class]
  apply congrArg (Polynomial.monomial 1)
  apply (RingCon.eq _).mpr
  exact RingConGen.Rel.of _ _ ⟨rfl, rfl⟩

def measuredRVQuotientGrading : MeasuredRVSpecialQuotient hc S →+* MeasuredRVGradingPolynomial hc S :=
  (measuredRVSpecialCongruence hc S).lift measuredRVPolynomialMap measuredRVPolynomialMap_respects

@[simp] theorem measuredRVQuotientGrading_class {k : ℕ} (U : MeasuredRVObject (M := M) S k) :
    measuredRVQuotientGrading ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc U)) =
      Polynomial.monomial k ((measuredRVSpecialCongruence hc S).mk' (measuredRVSemiringClass hc U)) :=
  measuredRVPolynomialMap_class U

theorem measuredRVQuotientGrading_fixed {k : ℕ} (a : MeasuredRVKPlus hc S k) :
    measuredRVQuotientGrading ((measuredRVSpecialCongruence hc S).mk' (measuredRVKPlusToSemiring hc a)) =
      Polynomial.monomial k ((measuredRVSpecialCongruence hc S).mk' (measuredRVKPlusToSemiring hc a)) := by
  obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
  rw [measuredRVKPlusToSemiring_class, measuredRVQuotientGrading_class]

end DiamondIntegral.Section3
