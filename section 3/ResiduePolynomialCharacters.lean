import «section 3».RVMonomialCharacters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Only nonzero coefficient summands require residue characters. -/
def residuePolynomialCharacters (P : KPolynomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) : Set (Fin n → ℤ) :=
  {e | ∃ i, rvMonomialCoefficient (P.terms i) a r ≠ 0 ∧ e = fun j => (P.terms i).powers j}

theorem residuePolynomialCharacters_finite (P : KPolynomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) : (residuePolynomialCharacters P a r).Finite := by
  apply (Set.finite_range (fun i => fun j => (P.terms i).powers j)).subset
  rintro e ⟨i,hi,rfl⟩
  exact Set.mem_range_self i

theorem residuePolynomialCharacters_value_finite (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hA : ∀ x ∈ A, P.Domain a r (fun i => (x i : CanonicalRV.RVSort M))) :
    ∀ e ∈ residuePolynomialCharacters P a r,
      (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  rintro e ⟨i,hc,rfl⟩
  exact rvMonomial_residue_character_values_finite (P.terms i) a r hc A (fun x hx => (hA x hx i).2)

theorem residuePolynomial_term_depends_on_characters (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ residuePolynomialCharacters P a r, integerCharacter e x = integerCharacter e y)
    (i : Fin P.size) :
    (P.terms i).rawEval a r (fun j => (x j : CanonicalRV.RVSort M)) =
      (P.terms i).rawEval a r (fun j => (y j : CanonicalRV.RVSort M)) := by
  by_cases hc : rvMonomialCoefficient (P.terms i) a r = 0
  · rw [rvMonomial_zero_coefficient _ a r hc,rvMonomial_zero_coefficient _ a r hc]
  · rw [rvMonomial_rawEval_units,rvMonomial_rawEval_units,hxy _ ⟨i,hc,rfl⟩]

theorem residuePolynomial_depends_on_characters (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ residuePolynomialCharacters P a r, integerCharacter e x = integerCharacter e y) :
    P.rawEval a r (fun j => (x j : CanonicalRV.RVSort M)) =
      P.rawEval a r (fun j => (y j : CanonicalRV.RVSort M)) := by
  apply congrArg KPolynomial.rvSum
  funext i
  exact residuePolynomial_term_depends_on_characters P a r x y hxy i

theorem residuePolynomial_domain_iff_of_characters (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ residuePolynomialCharacters P a r, integerCharacter e x = integerCharacter e y) :
    P.Domain a r (fun j => (x j : CanonicalRV.RVSort M)) ↔
      P.Domain a r (fun j => (y j : CanonicalRV.RVSort M)) := by
  unfold KPolynomial.Domain
  simp_rw [residuePolynomial_term_depends_on_characters P a r x y hxy]
end DiamondIntegral.Section3
