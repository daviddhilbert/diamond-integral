module

public import «section 4».PolynomialCoactionGrading
public import Mathlib.RingTheory.Polynomial.Subring

/-! The polynomial ring whose constant coefficient is restricted to a
specified subring has its natural grading, including degree zero. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.RestrictedPolynomialGrading

variable {R : Type*} [CommRing R] (A : Subring R)

def source : Subring (Polynomial R) := A.comap Polynomial.constantCoeff

theorem monomial_coefficient_mem (p : source A) (n : ℕ) :
    Polynomial.monomial n (p.val.coeff n) ∈ source A := by
  change (Polynomial.monomial n (p.val.coeff n)).coeff 0 ∈ A
  by_cases hn : n = 0
  · subst n
    rw [Polynomial.coeff_monomial_same]
    exact p.property
  · simp [Polynomial.coeff_monomial, hn]

theorem diagonal_coefficients (p : source A) :
    (↑(PolynomialDiagonal.diagonal p.val).coeffs : Set (Polynomial R)) ⊆ source A := by
  intro r hr
  obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hr
  rw [PolynomialDiagonal.diagonal_coeff]
  exact monomial_coefficient_mem A p n

def coactionFun (p : source A) : Polynomial (source A) :=
  (PolynomialDiagonal.diagonal p.val).toSubring (source A) (diagonal_coefficients A p)

theorem map_coactionFun (p : source A) :
    (coactionFun A p).map (source A).subtype = PolynomialDiagonal.diagonal p.val :=
  Polynomial.map_toSubring _ _ _

def coactionMap : source A →+* Polynomial (source A) where
  toFun := coactionFun A
  map_zero' := by
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    rw [map_coactionFun, Polynomial.map_zero]
    exact PolynomialDiagonal.diagonal.map_zero
  map_one' := by
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    rw [map_coactionFun, Polynomial.map_one]
    exact PolynomialDiagonal.diagonal.map_one
  map_add' p q := by
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    rw [map_coactionFun, Polynomial.map_add, map_coactionFun, map_coactionFun]
    exact PolynomialDiagonal.diagonal.map_add p.val q.val
  map_mul' p q := by
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    rw [map_coactionFun, Polynomial.map_mul, map_coactionFun, map_coactionFun]
    exact PolynomialDiagonal.diagonal.map_mul p.val q.val

theorem coaction_coefficient (p : source A) (n : ℕ) :
    ((coactionMap A p).coeff n : Polynomial R) = Polynomial.monomial n (p.val.coeff n) := by
  change ((coactionFun A p).coeff n : Polynomial R) = _
  rw [coactionFun, Polynomial.coeff_toSubring, PolynomialDiagonal.diagonal_coeff]

theorem diagonal_counit (p : Polynomial R) :
    Polynomial.eval 1 (PolynomialDiagonal.diagonal p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n r =>
    rw [PolynomialDiagonal.diagonal_monomial, Polynomial.eval_monomial, one_pow, mul_one]

def coaction : PolynomialCoactionGrading.Coaction (source A) where
  map := coactionMap A
  counit := by
    apply RingHom.ext
    intro p
    apply Subtype.ext
    change ((Polynomial.eval (1 : source A) (coactionMap A p) : source A) : Polynomial R) = p.val
    have he := Polynomial.eval_map_apply (source A).subtype (p := coactionMap A p) 1
    have hm : (coactionMap A p).map (source A).subtype = PolynomialDiagonal.diagonal p.val := map_coactionFun A p
    exact he.symm.trans (by rw [map_one, hm, diagonal_counit])
  coassoc := by
    apply RingHom.ext
    intro p
    apply Polynomial.ext
    intro n
    change ((coactionMap A p).map (coactionMap A)).coeff n =
      (PolynomialDiagonal.diagonal (coactionMap A p)).coeff n
    rw [Polynomial.coeff_map, PolynomialDiagonal.diagonal_coeff]
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    change (coactionFun A ((coactionMap A p).coeff n)).map (source A).subtype = _
    rw [map_coactionFun, Polynomial.map_monomial, coaction_coefficient,
      PolynomialDiagonal.diagonal_monomial]
    change Polynomial.monomial n (Polynomial.monomial n (p.val.coeff n)) =
      Polynomial.monomial n (((coactionMap A p).coeff n : source A) : Polynomial R)
    rw [coaction_coefficient]

def piece (n : ℕ) : AddSubgroup (source A) := (coaction A).piece n

instance gradedRing : GradedRing (piece A) := (coaction A).grading

theorem mem_piece (p : source A) (n : ℕ) :
    p ∈ piece A n ↔ p.val = Polynomial.monomial n (p.val.coeff n) := by
  constructor
  · intro hp
    change coactionMap A p = Polynomial.monomial n p at hp
    have hc := congrArg (fun f : Polynomial (source A) => ((f.coeff n : source A) : Polynomial R)) hp
    simpa only [Polynomial.coeff_monomial_same, coaction_coefficient] using hc.symm
  · intro hp
    change coactionMap A p = Polynomial.monomial n p
    apply Polynomial.map_injective (source A).subtype (source A).subtype_injective
    change (coactionFun A p).map (source A).subtype = _
    rw [map_coactionFun, Polynomial.map_monomial, hp, PolynomialDiagonal.diagonal_monomial]
    exact congrArg (Polynomial.monomial n) hp.symm

end DiamondIntegral.Section4.RestrictedPolynomialGrading
