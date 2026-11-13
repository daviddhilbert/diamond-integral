module

public import «section 4».PolynomialCoactionQuotient
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! Degree-preserving maps commute with grading coactions, and factor
through homogeneous quotients as graded maps when their kernels contain
the quotient ideal. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
variable {R S : Type*} [CommRing R] [CommRing S]
variable (c : Coaction R) (e : Coaction S) (f : R →+* S)

theorem map_coaction_of_mem
    (hf : ∀ n x, x ∈ c.piece n → f x ∈ e.piece n) :
    (Polynomial.mapRingHom f).comp c.map = e.map.comp f := by
  apply RingHom.ext
  intro x
  change (c.map x).map f = e.map (f x)
  rw [← c.sum_coefficients x]
  simp only [map_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show c.map ((c.map x).coeff n) = Polynomial.monomial n ((c.map x).coeff n) from c.coefficient_mem x n,
    Polynomial.map_monomial]
  exact (hf n _ (c.coefficient_mem x n)).symm

theorem quotientLift_mem (I : Ideal R)
    (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    (hker : ∀ x ∈ I, f x = 0)
    (hf : ∀ n x, x ∈ c.piece n → f x ∈ e.piece n)
    {n : ℕ} {x : R ⧸ I} (hx : x ∈ (c.quotient I hI).piece n) :
    Ideal.Quotient.lift I f hker x ∈ e.piece n := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have heq : Ideal.Quotient.mk I ((c.map r).coeff n) = Ideal.Quotient.mk I r := by
    have he := congrArg (fun p : Polynomial (R ⧸ I) => p.coeff n) hx
    change (((c.map r).map (Ideal.Quotient.mk I)).coeff n) = (Polynomial.monomial n (Ideal.Quotient.mk I r)).coeff n at he
    simpa only [Polynomial.coeff_map, Polynomial.coeff_monomial, ite_true] using he
  rw [← heq]
  exact hf n _ (c.coefficient_mem r n)

def gradedQuotientLift (I : Ideal R)
    (hI : ∀ n x, x ∈ I → (c.map x).coeff n ∈ I)
    (hker : ∀ x ∈ I, f x = 0)
    (hf : ∀ n x, x ∈ c.piece n → f x ∈ e.piece n) :
    GradedRingHom (c.quotient I hI).piece e.piece where
  toRingHom := Ideal.Quotient.lift I f hker
  map_mem := c.quotientLift_mem e f I hI hker hf

end DiamondIntegral.Section4.PolynomialCoactionGrading.Coaction
