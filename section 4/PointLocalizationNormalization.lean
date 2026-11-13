import «section 4».PolynomialCoactionGrading
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! A polynomial grading coaction normalizes every homogeneous element
of degree n to x/q^n in the degree-zero localization at a degree-one
element q. The whole-ring normalization map is constructed by evaluating
the coaction at q inverse; no nonzerodivisor assumption is needed. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.PointLocalizationNormalization
open PolynomialCoactionGrading
variable {R : Type*} [CommRing R]
variable (c : Coaction R) (q : R)

local instance coactionGradedRing : GradedRing c.piece := c.grading

def evaluation : R →+* Localization.Away q :=
  (Polynomial.eval₂RingHom (algebraMap R (Localization.Away q)) (IsLocalization.Away.invSelf q)).comp c.map

theorem evaluation_homogeneous {n : ℕ} {x : R} (hx : x ∈ c.piece n) :
    evaluation c q x = algebraMap R (Localization.Away q) x * IsLocalization.Away.invSelf q ^ n := by
  change Polynomial.eval₂ _ _ (c.map x) = _
  change c.map x = Polynomial.monomial n x at hx
  rw [hx, Polynomial.eval₂_monomial]

theorem evaluation_fraction {n : ℕ} {x : R} (hx : x ∈ c.piece n) :
    evaluation c q x = Localization.mk x (⟨q ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers q) := by
  rw [evaluation_homogeneous c q hx, Localization.mk_eq_mk'_apply]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change (algebraMap R (Localization.Away q) x * IsLocalization.Away.invSelf q ^ n) *
    algebraMap R (Localization.Away q) (q ^ n) = algebraMap R (Localization.Away q) x
  rw [map_pow, mul_assoc, ← mul_pow]
  rw [mul_comm (IsLocalization.Away.invSelf q), IsLocalization.Away.mul_invSelf, one_pow, mul_one]

abbrev Source := HomogeneousLocalization.Away c.piece q

def embedding : Source c q →+* Localization.Away q := algebraMap _ _

theorem embedding_injective : Function.Injective (embedding c q) :=
  HomogeneousLocalization.val_injective (Submonoid.powers q)

theorem evaluation_homogeneous_mem (hq : q ∈ c.piece 1) {n : ℕ} {x : R} (hx : x ∈ c.piece n) :
    evaluation c q x ∈ (embedding c q).range := by
  let z : Source c q := HomogeneousLocalization.Away.mk c.piece hq n x (by
    simpa only [smul_eq_mul, mul_one] using hx)
  refine ⟨z, ?_⟩
  exact (evaluation_fraction c q hx).symm

theorem evaluation_mem (hq : q ∈ c.piece 1) (x : R) : evaluation c q x ∈ (embedding c q).range := by
  rw [← c.sum_coefficients x, map_sum]
  apply (embedding c q).range.sum_mem
  intro n hn
  exact evaluation_homogeneous_mem c q hq (c.coefficient_mem x n)

def rangeEquiv : Source c q ≃+* (embedding c q).range :=
  RingEquiv.ofBijective (embedding c q).rangeRestrict
    ⟨(fun _ _ h => embedding_injective c q (congrArg Subtype.val h)), (embedding c q).rangeRestrict_surjective⟩

def normalize (hq : q ∈ c.piece 1) : R →+* Source c q :=
  (rangeEquiv c q).symm.toRingHom.comp ((evaluation c q).codRestrict (embedding c q).range (evaluation_mem c q hq))

theorem embedding_normalize (hq : q ∈ c.piece 1) (x : R) :
    embedding c q (normalize c q hq x) = evaluation c q x :=
  congrArg Subtype.val ((rangeEquiv c q).apply_symm_apply ⟨evaluation c q x, evaluation_mem c q hq x⟩)

theorem normalize_homogeneous (hq : q ∈ c.piece 1) {n : ℕ} {x : R} (hx : x ∈ c.piece n) :
    normalize c q hq x = HomogeneousLocalization.Away.mk c.piece hq n x (by
      simpa only [smul_eq_mul, mul_one] using hx) := by
  apply embedding_injective c q
  rw [embedding_normalize, evaluation_fraction c q hx]
  rfl

theorem normalize_point (hq : q ∈ c.piece 1) : normalize c q hq q = 1 := by
  apply embedding_injective c q
  rw [embedding_normalize, map_one, evaluation_homogeneous c q hq, pow_one]
  exact IsLocalization.Away.mul_invSelf q

end DiamondIntegral.Section4.PointLocalizationNormalization
