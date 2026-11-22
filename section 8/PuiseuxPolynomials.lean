import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Ideal.Span
import «section 6».FiniteApertureSpecializationFactors

/-! Notation 8.1 and the algebra of Lemma 8.3.

The ring `R[T^ℚ]` of Puiseux polynomials is the group ring of `ℚ` over `R`.
Laurent polynomials embed in it, and `η` sends `T` to a unit `L` of `R`
(in the paper `R = K^μ̂ Var_ℂ[[𝔸]⁻¹]` and `L = [𝔸]`).

`η` is only defined on Laurent polynomials. To use it on the natural subring
of a ring `B` with a homomorphism `h : B → R[T^ℚ]`, we use the projection
`integerPart` onto integer exponents, which is linear over Laurent
polynomials. If `h` sends every generator of an ideal `J` into the principal
ideal of `L T⁻¹ - 1`, then `η ∘ h` vanishes on `J ∩ B^♮`, also when the
coefficients of an element of `J` lie outside `B^♮`. -/

noncomputable section
open Classical

namespace DiamondIntegral.Section8

open LaurentPolynomial

variable (R : Type*) [CommRing R]

/-- Notation 8.1: the ring `R[T^ℚ]` of Puiseux polynomials over `R`. -/
abbrev PuiseuxPolynomial := AddMonoidAlgebra R ℚ

namespace PuiseuxPolynomial

/-- The inclusion `R[T, T⁻¹] → R[T^ℚ]`. -/
def ofLaurent : R[T;T⁻¹] →+* PuiseuxPolynomial R :=
  AddMonoidAlgebra.mapDomainRingHom R (Int.castAddHom ℚ)

theorem ofLaurent_single (n : ℤ) (r : R) :
    ofLaurent R (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single (n : ℚ) r :=
  AddMonoidAlgebra.mapDomain_single

theorem ofLaurent_injective : Function.Injective (ofLaurent R) :=
  AddMonoidAlgebra.mapDomain_injective Int.cast_injective

/-- The part of a Puiseux polynomial with integer exponents. -/
def integerPart : PuiseuxPolynomial R →+ R[T;T⁻¹] :=
  AddMonoidAlgebra.comapDomainAddMonoidHom Int.cast Int.cast_injective

theorem integerPart_single_int (n : ℤ) (r : R) :
    integerPart R (AddMonoidAlgebra.single (n : ℚ) r) = AddMonoidAlgebra.single n r :=
  AddMonoidAlgebra.comapDomain_single_map Int.cast Int.cast_injective n r

theorem integerPart_single_of_not_int {q : ℚ} (hq : q ∉ Set.range (Int.cast : ℤ → ℚ)) (r : R) :
    integerPart R (AddMonoidAlgebra.single q r) = 0 := by
  refine LaurentPolynomial.ext fun k => ?_
  have hk : q ≠ (k : ℚ) := fun h => hq ⟨k, h.symm⟩
  show (AddMonoidAlgebra.comapDomain Int.cast Int.cast_injective
    (AddMonoidAlgebra.single q r)).coeff k = 0
  rw [AddMonoidAlgebra.coeff_comapDomain, Finsupp.comapDomain_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  simp [hk]

theorem integerPart_ofLaurent (a : R[T;T⁻¹]) : integerPart R (ofLaurent R a) = a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single n r => rw [ofLaurent_single, integerPart_single_int]

/-- `integerPart` is linear over Laurent polynomials. -/
theorem integerPart_mul (a : R[T;T⁻¹]) (x : PuiseuxPolynomial R) :
    integerPart R (ofLaurent R a * x) = a * integerPart R x := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [map_add, add_mul, map_add, ha, hb, add_mul]
  | single n r =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
    | single q s =>
      rw [ofLaurent_single, AddMonoidAlgebra.single_mul_single]
      by_cases hq : q ∈ Set.range (Int.cast : ℤ → ℚ)
      · obtain ⟨k, rfl⟩ := hq
        rw [← Int.cast_add, integerPart_single_int, integerPart_single_int,
          AddMonoidAlgebra.single_mul_single]
      · rw [integerPart_single_of_not_int R hq, mul_zero]
        apply integerPart_single_of_not_int
        rintro ⟨k, hk⟩
        exact hq ⟨k - n, by push_cast; linarith⟩

/-- The Laurent polynomials as a subring of `R[T^ℚ]`. -/
def laurentSubring : Subring (PuiseuxPolynomial R) := (ofLaurent R).range

theorem ofLaurent_integerPart {x : PuiseuxPolynomial R} (hx : x ∈ laurentSubring R) :
    ofLaurent R (integerPart R x) = x := by
  obtain ⟨a, rfl⟩ := hx
  rw [integerPart_ofLaurent]

variable {R}

/-- Notation 8.1: the homomorphism `η : R[T, T⁻¹] → R` with `T ↦ L`. -/
def eta (L : Rˣ) : R[T;T⁻¹] →+* R := LaurentPolynomial.eval₂ (RingHom.id R) L

/-- `L T⁻¹ - 1`, the common factor of the images of the annular relations. -/
def annularElement (L : Rˣ) : R[T;T⁻¹] := C (L : R) * T (-1) - 1

theorem eta_annularElement (L : Rˣ) : eta L (annularElement L) = 0 := by
  simp [eta, annularElement]

/-- `η` kills the integer part of every multiple of `L T⁻¹ - 1`. -/
theorem eta_integerPart_of_mem_span (L : Rˣ) {x : PuiseuxPolynomial R}
    (hx : x ∈ Ideal.span {ofLaurent R (annularElement L)}) :
    eta L (integerPart R x) = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [mul_comm, integerPart_mul, map_mul, eta_annularElement, zero_mul]

/-- The image of an annular relation: weight `q`, coefficient `a`, aperture depth `n` (in units
of `1/m`). It is a multiple of `L T⁻¹ - 1`. -/
theorem annular_mem_span (L : Rˣ) (q : ℚ) (a : R) (n : ℕ) :
    AddMonoidAlgebra.single q a *
        ofLaurent R (Section6.ApertureSpecializationTest.annularFactor (C (L : R)) (T (-1)) n)
      ∈ Ideal.span {ofLaurent R (annularElement L)} := by
  rw [Section6.ApertureSpecializationTest.annularFactor_eq, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

section Natural

variable {B : Type*} [CommRing B] (h : B →+* PuiseuxPolynomial R)

/-- The natural subring `B^♮ = h⁻¹(R[T, T⁻¹])` of a ring `B` over `R[T^ℚ]`. -/
def natural : Subring B := (laurentSubring R).comap h

/-- `η ∘ h` on the natural subring. -/
def etaNatural (L : Rˣ) : natural h →+* R where
  toFun x := eta L (integerPart R (h x))
  map_one' := by
    have : h (1 : B) = ofLaurent R 1 := by rw [map_one, map_one]
    show eta L (integerPart R (h 1)) = 1
    rw [this, integerPart_ofLaurent, map_one]
  map_mul' x y := by
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    have hx : h x = ofLaurent R a := ha.symm
    have hy : h y = ofLaurent R b := hb.symm
    simp only [Subring.coe_mul, map_mul, hx, hy]
    rw [← map_mul, integerPart_ofLaurent, integerPart_ofLaurent, integerPart_ofLaurent, map_mul]
  map_zero' := by simp
  map_add' x y := by simp

theorem etaNatural_apply (L : Rˣ) (x : natural h) :
    etaNatural h L x = eta L (integerPart R (h x)) := rfl

/-- Lemma 8.3, algebraic part. If `h` sends every generator of an ideal into the principal ideal
of `L T⁻¹ - 1`, then `η ∘ h` vanishes on the intersection of the ideal with the natural subring.
The coefficients of the element in terms of the generators need not be natural. -/
theorem etaNatural_eq_zero (L : Rˣ) (G : Set B)
    (hG : ∀ g ∈ G, h g ∈ Ideal.span {ofLaurent R (annularElement L)})
    (x : natural h) (hx : (x : B) ∈ Ideal.span G) : etaNatural h L x = 0 := by
  apply eta_integerPart_of_mem_span
  have : Ideal.span G ≤ (Ideal.span {ofLaurent R (annularElement L)}).comap h :=
    Ideal.span_le.mpr hG
  exact this hx

end Natural

end PuiseuxPolynomial

end DiamondIntegral.Section8
