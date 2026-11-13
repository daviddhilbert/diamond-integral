import «section 3».RawResidueSum
import «section 3».RVMonomialValueDependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvMonomial_inK_iff_of_values (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    ValuedModelMap.inK (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) ↔
      ValuedModelMap.inK (T.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) := by
  have he := rvMonomial_absolute_depends_on_values T a r x y hv
  rw [RVOperations.inK_iff,RVOperations.inK_iff,
    ← RVOperations.absolute_eq_zero,← RVOperations.absolute_eq_zero,he]

def polynomialResiduePattern (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : Prop :=
  ∀ i, ValuedModelMap.inK ((P.terms i).rawEval a r (fun j => (x j : CanonicalRV.RVSort M))) ↔ mask i = true

def maskedPolynomialCharacters (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool) : Set (Fin n → ℤ) :=
  {e | ∃ i, mask i = true ∧ rvMonomialCoefficient (P.terms i) a r ≠ 0 ∧ e = fun j => (P.terms i).powers j}

theorem maskedPolynomialCharacters_finite (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool) :
    (maskedPolynomialCharacters P a r mask).Finite := by
  apply (Set.finite_range (fun i => fun j => (P.terms i).powers j)).subset
  rintro e ⟨i,_,_,rfl⟩
  exact Set.mem_range_self i

theorem maskedPolynomialCharacters_value_finite (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (hA : ∀ x ∈ A, polynomialResiduePattern P a r mask x) :
    ∀ e ∈ maskedPolynomialCharacters P a r mask, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  rintro e ⟨i,hmask,hc,rfl⟩
  exact rvMonomial_residue_character_values_finite (P.terms i) a r hc A (fun x hx => (hA x hx i).mpr hmask)

theorem polynomialResiduePattern_iff_of_values (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    polynomialResiduePattern P a r mask x ↔ polynomialResiduePattern P a r mask y := by
  unfold polynomialResiduePattern
  simp_rw [rvMonomial_inK_iff_of_values _ a r x y hv]

/-- Total flat-sum semantics respects the global value pattern. The
original pole and residue-domain guards are preserved separately. -/
theorem maskedPolynomial_depends_on_characters (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (mask : Fin P.size → Bool)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hmask : polynomialResiduePattern P a r mask x)
    (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i))
    (hxy : ∀ e ∈ maskedPolynomialCharacters P a r mask, integerCharacter e x = integerCharacter e y) :
    P.rawEval a r (fun j => (x j : CanonicalRV.RVSort M)) = P.rawEval a r (fun j => (y j : CanonicalRV.RVSort M)) := by
  apply residueSum_selective_congr
  · intro i
    exact rvMonomial_inK_iff_of_values (P.terms i) a r x y hv
  · intro i hi
    by_cases hc : rvMonomialCoefficient (P.terms i) a r = 0
    · rw [rvMonomial_zero_coefficient _ a r hc,rvMonomial_zero_coefficient _ a r hc]
    · rw [rvMonomial_rawEval_units,rvMonomial_rawEval_units,hxy _ ⟨i,(hmask i).mp hi,hc,rfl⟩]

theorem residuePolynomial_domain_iff_of_values (P : KPolynomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    P.Domain a r (fun j => (x j : CanonicalRV.RVSort M)) ↔ P.Domain a r (fun j => (y j : CanonicalRV.RVSort M)) := by
  unfold KPolynomial.Domain
  simp_rw [rvMonomial_inK_iff_of_values _ a r x y hv]
end DiamondIntegral.Section3
