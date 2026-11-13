import «section 3».ResiduePolynomialCharacters
import «section 3».RVMonomialRatios
import «section 3».RVMonomialValueDependence
import «section 3».GuardedEqualityValueSplit
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def equalityRatioCharacter (E : EqualityPayload I R (Fin n)) : Fin n → ℤ :=
  fun i => E.right.powers i - E.left.powers i

def equalityActiveCharacters (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool) : Set (Fin n → ℤ) :=
  (residuePolynomialCharacters E.leftK a r ∪ residuePolynomialCharacters E.rightK a r) ∪
    {e | same = true ∧ rvMonomialCoefficient E.left a r ≠ 0 ∧ rvMonomialCoefficient E.right a r ≠ 0 ∧
      e = equalityRatioCharacter E}

theorem equalityActiveCharacters_finite (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool) :
    (equalityActiveCharacters E a r same).Finite :=
  ((residuePolynomialCharacters_finite E.leftK a r).union
    (residuePolynomialCharacters_finite E.rightK a r)).union
      ((Set.finite_singleton (equalityRatioCharacter E)).subset (fun e he => he.2.2.2))

theorem equalityActiveCharacters_value_finite (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hD : ∀ x ∈ A, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) (.equality E true))
    (hmask : ∀ x ∈ A,
      (RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
       RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))) ↔ same = true) :
    ∀ e ∈ equalityActiveCharacters E a r same, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  rintro e ((he | he) | ⟨hs,hL,hR,rfl⟩)
  · exact residuePolynomialCharacters_value_finite E.leftK a r A (fun x hx => (hD x hx).2.1) e he
  · exact residuePolynomialCharacters_value_finite E.rightK a r A (fun x hx => (hD x hx).2.2.2) e he
  · apply rvMonomial_ratio_character_values_finite E.right E.left a r hR hL A
    intro x hx
    exact residue_ratio_of_equal_values _ _ (rvMonomial_rawEval_ne_zero E.left a r hL x) ((hmask x hx).mpr hs)

theorem equality_domain_iff_of_active_characters (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ equalityActiveCharacters E a r same, integerCharacter e x = integerCharacter e y) :
    RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) (.equality E true) ↔
      RVLiteral.Domain a r (fun i => (y i : CanonicalRV.RVSort M)) (.equality E true) := by
  have hL := residuePolynomial_domain_iff_of_characters E.leftK a r x y
    (fun e he => hxy e (Or.inl (Or.inl he)))
  have hR := residuePolynomial_domain_iff_of_characters E.rightK a r x y
    (fun e he => hxy e (Or.inl (Or.inr he)))
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  rw [hL,hR]
end DiamondIntegral.Section3
