module

public import «section 4».PolynomialCoactionGrading
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Polynomial grading coactions descend through homogeneous ideals. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction

variable {R : Type*} [CommRing R]
variable (c : Coaction R) (I : Ideal R)

def quotientMap (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I) :
    R ⧸ I →+* Polynomial (R ⧸ I) :=
  Ideal.Quotient.lift I ((Polynomial.mapRingHom (Ideal.Quotient.mk I)).comp c.map) (by
    intro x hx
    apply Polynomial.ext
    intro n
    change ((c.map x).map (Ideal.Quotient.mk I)).coeff n = (0 : Polynomial (R ⧸ I)).coeff n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI n x hx))

theorem quotientMap_mk (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I) (x : R) :
    c.quotientMap I hI (Ideal.Quotient.mk I x) = (c.map x).map (Ideal.Quotient.mk I) := rfl

def quotient (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I) : Coaction (R ⧸ I) where
  map := c.quotientMap I hI
  counit := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change Polynomial.eval 1 (c.quotientMap I hI (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk I x
    rw [c.quotientMap_mk, Polynomial.eval_map, Polynomial.eval₂_at_one]
    exact congrArg (Ideal.Quotient.mk I) (RingHom.congr_fun c.counit x)
  coassoc := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    apply Polynomial.ext
    intro n
    change ((c.quotientMap I hI (Ideal.Quotient.mk I x)).map (c.quotientMap I hI)).coeff n =
      (PolynomialDiagonal.diagonal (c.quotientMap I hI (Ideal.Quotient.mk I x))).coeff n
    rw [Polynomial.coeff_map, PolynomialDiagonal.diagonal_coeff, c.quotientMap_mk,
      Polynomial.coeff_map, c.quotientMap_mk]
    have hc := c.coefficient_mem x n
    change c.map ((c.map x).coeff n) = Polynomial.monomial n ((c.map x).coeff n) at hc
    rw [hc, Polynomial.map_monomial]

theorem quotient_mem (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    {n : ℕ} {x : R} (hx : x ∈ c.piece n) :
    Ideal.Quotient.mk I x ∈ (c.quotient I hI).piece n := by
  change c.map x = Polynomial.monomial n x at hx
  change c.quotientMap I hI (Ideal.Quotient.mk I x) = Polynomial.monomial n (Ideal.Quotient.mk I x)
  rw [c.quotientMap_mk, hx, Polynomial.map_monomial]

theorem decompose_coefficient (x : R) (n : ℕ) :
    letI := c.grading
    ((DirectSum.decompose c.piece x n : c.piece n) : R) = (c.map x).coeff n := by
  letI := c.grading
  change ((c.decompose x n : c.piece n) : R) = _
  exact c.decompose_apply x n

theorem homogeneous_ideal_coefficients :
    letI := c.grading
    I.IsHomogeneous c.piece → ∀ n x, x ∈ I → (c.map x).coeff n ∈ I := by
  letI := c.grading
  intro hI n x hx
  rw [← c.decompose_coefficient x n]
  exact hI n hx

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
