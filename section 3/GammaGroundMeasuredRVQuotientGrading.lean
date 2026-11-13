import «section 3».GammaGroundMeasuredRVGenerators
import «section 3».PresentationHomExt
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

abbrev GammaGroundMeasuredRVSpecialQuotient (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  (gammaGroundMeasuredRVSpecialCongruence (M := M) hc ground).Quotient

local instance gammaGroundMeasuredRVGradingCoefficientSemiring : Semiring (GammaGroundMeasuredRVSpecialQuotient hc ground) :=
  (inferInstance : CommSemiring (GammaGroundMeasuredRVSpecialQuotient hc ground)).toSemiring

abbrev GammaGroundMeasuredRVGradingPolynomial (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Polynomial (GammaGroundMeasuredRVSpecialQuotient hc ground)

theorem gammaGroundMeasuredRVSpecialMap_zero :
    (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' 0 = (0 : GammaGroundMeasuredRVSpecialQuotient hc ground) := rfl

theorem gammaGroundMeasuredRVSpecialMap_one :
    (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' 1 = (1 : GammaGroundMeasuredRVSpecialQuotient hc ground) := rfl

theorem gammaGroundMeasuredRVSpecialMap_add (a b : GammaGroundMeasuredRVPositiveSemiring hc ground) :
    (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (a + b) =
      (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' a + (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' b := rfl

theorem gammaGroundMeasuredRVSpecialMap_mul (a b : GammaGroundMeasuredRVPositiveSemiring hc ground) :
    (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (a * b) =
      (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' a * (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' b := rfl

theorem gammaGroundMeasuredRVMonomial_add (k : ℕ) (a b : GammaGroundMeasuredRVSpecialQuotient hc ground) :
    (Polynomial.monomial k (a + b) : GammaGroundMeasuredRVGradingPolynomial hc ground) =
      Polynomial.monomial k a + Polynomial.monomial k b :=
  (Polynomial.monomial k).map_add' a b

def gammaGroundMeasuredRVPolynomialInvariant : PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc ground)
    (R := GammaGroundMeasuredRVGradingPolynomial hc ground) where
  toFun A := Polynomial.monomial A.1
    ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass A.2))
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (fun x => Polynomial.monomial k ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' x))
      (gammaGroundMeasuredRVSemiringClass_iso e)
  empty := by
    change Polynomial.monomial 0 ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.empty hc ground 0))) = 0
    rw [gammaGroundMeasuredRVSemiringClass_empty, gammaGroundMeasuredRVSpecialMap_zero, Polynomial.monomial_zero_right]
  unit := by
    change Polynomial.monomial 0 ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.unit hc ground))) = 1
    rw [gammaGroundMeasuredRVSemiringClass_unit, gammaGroundMeasuredRVSpecialMap_one]
    exact Polynomial.monomial_zero_one
  product A B := by
    change Polynomial.monomial (A.1 + B.1) ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass (A.2.product B.2))) = _
    rw [gammaGroundMeasuredRVSemiringClass_product, gammaGroundMeasuredRVSpecialMap_mul, Polynomial.monomial_mul_monomial]
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      have hq := congrArg (gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass_scissor hs)
      rw [gammaGroundMeasuredRVSpecialMap_add, gammaGroundMeasuredRVSpecialMap_add] at hq
      have ht := congrArg (fun q : GammaGroundMeasuredRVSpecialQuotient hc ground =>
        (Polynomial.monomial k q : GammaGroundMeasuredRVGradingPolynomial hc ground)) hq
      rw [gammaGroundMeasuredRVMonomial_add, gammaGroundMeasuredRVMonomial_add] at ht
      exact ht
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [gammaGroundMeasuredRVSemiringClass_empty, gammaGroundMeasuredRVSpecialMap_zero, Polynomial.monomial_zero_right, add_zero]

def gammaGroundMeasuredRVPolynomialMap : GammaGroundMeasuredRVPositiveSemiring hc ground →+* GammaGroundMeasuredRVGradingPolynomial hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredRVSemiringPresentation hc ground) gammaGroundMeasuredRVPolynomialInvariant

@[simp] theorem gammaGroundMeasuredRVPolynomialMap_class {k : ℕ} (U : GammaGroundMeasuredRVObject (M := M) hc ground k) :
    gammaGroundMeasuredRVPolynomialMap (gammaGroundMeasuredRVSemiringClass U) =
      Polynomial.monomial k ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass U)) :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc ground) gammaGroundMeasuredRVPolynomialInvariant ⟨k, U⟩

theorem gammaGroundMeasuredRVPolynomialMap_respects :
    gammaGroundMeasuredRVSpecialCongruence hc ground ≤ RingCon.ker (gammaGroundMeasuredRVPolynomialMap (hc := hc) (ground := ground)) := by
  apply RingCon.ringConGen_le.mpr
  rintro x y ⟨rfl, rfl⟩
  change gammaGroundMeasuredRVPolynomialMap _ = gammaGroundMeasuredRVPolynomialMap _
  rw [gammaGroundMeasuredRVPolynomialMap_class, gammaGroundMeasuredRVPolynomialMap_class]
  apply congrArg (Polynomial.monomial 1)
  apply (RingCon.eq _).mpr
  exact RingConGen.Rel.of _ _ ⟨rfl, rfl⟩

def gammaGroundMeasuredRVQuotientGrading : GammaGroundMeasuredRVSpecialQuotient hc ground →+* GammaGroundMeasuredRVGradingPolynomial hc ground :=
  (gammaGroundMeasuredRVSpecialCongruence hc ground).lift gammaGroundMeasuredRVPolynomialMap gammaGroundMeasuredRVPolynomialMap_respects

@[simp] theorem gammaGroundMeasuredRVQuotientGrading_class {k : ℕ} (U : GammaGroundMeasuredRVObject (M := M) hc ground k) :
    gammaGroundMeasuredRVQuotientGrading ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass U)) =
      Polynomial.monomial k ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVSemiringClass U)) :=
  gammaGroundMeasuredRVPolynomialMap_class U

theorem gammaGroundMeasuredRVQuotientGrading_fixed {k : ℕ} (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVQuotientGrading ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring a)) =
      Polynomial.monomial k ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring a)) := by
  let F : GammaGroundMeasuredRVKPlus hc ground k →+ GammaGroundMeasuredRVGradingPolynomial hc ground := {
    toFun := fun x => gammaGroundMeasuredRVQuotientGrading
      ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring x))
    map_zero' := by
      change gammaGroundMeasuredRVQuotientGrading
        ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring (0 : GammaGroundMeasuredRVKPlus hc ground k))) = 0
      rw [map_zero, gammaGroundMeasuredRVSpecialMap_zero]
      exact gammaGroundMeasuredRVQuotientGrading.map_zero
    map_add' := fun x y => by
      rw [gammaGroundMeasuredRVKPlusToSemiring.map_add, gammaGroundMeasuredRVSpecialMap_add]
      exact gammaGroundMeasuredRVQuotientGrading.map_add' _ _ }
  let B : GammaGroundMeasuredRVKPlus hc ground k →+ GammaGroundMeasuredRVGradingPolynomial hc ground := {
    toFun := fun x => Polynomial.monomial k
      ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring x))
    map_zero' := by rw [map_zero, gammaGroundMeasuredRVSpecialMap_zero, Polynomial.monomial_zero_right]
    map_add' := fun x y => by rw [map_add, gammaGroundMeasuredRVSpecialMap_add, gammaGroundMeasuredRVMonomial_add] }
  have he : F = B := by
    apply positiveAdditivePresentationHom_ext (gammaGroundMeasuredRVPresentation hc ground k)
    intro U
    change gammaGroundMeasuredRVQuotientGrading
      ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk' (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U))) =
      Polynomial.monomial k ((gammaGroundMeasuredRVSpecialCongruence hc ground).mk'
        (gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U)))
    rw [gammaGroundMeasuredRVKPlusToSemiring_class]
    exact gammaGroundMeasuredRVQuotientGrading_class U
  exact DFunLike.congr_fun he a

end DiamondIntegral.Section3
