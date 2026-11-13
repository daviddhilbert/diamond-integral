import «section 4».FieldFiniteCharacters
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Lattice

/-! The affine-line class is transcendental over the integers in the
pure-field definable Grothendieck presentation. The proof specializes a
finite proposed relation at arbitrarily large finite-field cardinalities. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FieldAffineTranscendence
open FieldDefinableRing
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [FirstOrder.Ring.CompatibleRing K]

def freePolynomial : Polynomial ℤ →+* FreeCommRing (Chart K) :=
  Polynomial.eval₂RingHom (Int.castRingHom _) (FreeCommRing.of (affine K))

theorem polynomial_not_mem (P : Polynomial ℤ) (hP : P ≠ 0) :
    freePolynomial K P ∉ relationIdeal K := by
  intro hmem
  obtain ⟨s, hs, hsmem⟩ := Submodule.mem_span_finite_of_mem_span hmem
  obtain ⟨b, hb⟩ := Polynomial.exists_max_root P hP
  obtain ⟨q, hq, _, f, hfaff, hf⟩ := FieldFiniteCharacters.exists_large K s hs b.natAbs
  have hkill : Ideal.span (s : Set (FreeCommRing (Chart K))) ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro r hr
    exact hf r hr
  have hzero : f (freePolynomial K P) = 0 := hkill hsmem
  have hcoeff : f.comp (Int.castRingHom _) = RingHom.id ℤ := Subsingleton.elim _ _
  change f (P.eval₂ (Int.castRingHom _) (FreeCommRing.of (affine K))) = 0 at hzero
  rw [Polynomial.hom_eval₂, hcoeff, hfaff, Polynomial.eval₂_id] at hzero
  have hle : (q : ℤ) ≤ b := hb q hzero
  have habs : b ≤ (b.natAbs : ℤ) := Int.le_natAbs
  exact (not_lt_of_ge (hle.trans habs)) (Int.ofNat_lt.mpr hq)

def polynomial : Polynomial ℤ →+* FieldDefinableRing.Ring K :=
  (Ideal.Quotient.mk (relationIdeal K)).comp (freePolynomial K)

theorem polynomial_X : polynomial K Polynomial.X = affineClass K := by
  change Ideal.Quotient.mk (relationIdeal K)
    (Polynomial.eval₂ (Int.castRingHom _) (FreeCommRing.of (affine K)) Polynomial.X) = _
  rw [Polynomial.eval₂_X]
  rfl

theorem polynomial_injective : Function.Injective (polynomial K) := by
  apply (injective_iff_map_eq_zero (polynomial K)).mpr
  intro P hP
  by_contra hn
  exact polynomial_not_mem K P hn (Ideal.Quotient.eq_zero_iff_mem.mp hP)

theorem affine_ne_one : affineClass K ≠ 1 := by
  intro h
  have he : polynomial K Polynomial.X = polynomial K 1 := by
    simpa only [polynomial_X, map_one] using h
  have he' := congrArg (fun P : Polynomial ℤ => P.coeff 0) ((polynomial_injective K) he)
  simpa using he'

theorem affine_pow_ne_zero (n : ℕ) : affineClass K ^ n ≠ 0 := by
  intro h
  have he : polynomial K (Polynomial.X ^ n) = polynomial K 0 := by
    simpa only [map_pow, polynomial_X, map_zero] using h
  exact (pow_ne_zero n Polynomial.X_ne_zero) ((polynomial_injective K) he)

end DiamondIntegral.Section4.FieldAffineTranscendence
