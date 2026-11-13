import «section 3».MaskedResiduePolynomials
import «section 3».RVMonomialRatios
import «section 3».EqualityCharacters
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


abbrev EqualityValuePattern (E : EqualityPayload I R (Fin n)) :=
  Bool × (Fin E.leftK.size → Bool) × (Fin E.rightK.size → Bool)

def equalityPatternCell (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : Prop :=
  ((RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
    RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))) ↔ p.1 = true) ∧
    polynomialResiduePattern E.leftK a r p.2.1 x ∧ polynomialResiduePattern E.rightK a r p.2.2 x

def maskedEqualityCharacters (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E) : Set (Fin n → ℤ) :=
  (maskedPolynomialCharacters E.leftK a r p.2.1 ∪ maskedPolynomialCharacters E.rightK a r p.2.2) ∪
    {e | p.1 = true ∧ rvMonomialCoefficient E.left a r ≠ 0 ∧ rvMonomialCoefficient E.right a r ≠ 0 ∧
      e = equalityRatioCharacter E}

theorem maskedEqualityCharacters_finite (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E) :
    (maskedEqualityCharacters E a r p).Finite :=
  ((maskedPolynomialCharacters_finite E.leftK a r p.2.1).union
    (maskedPolynomialCharacters_finite E.rightK a r p.2.2)).union
      ((Set.finite_singleton (equalityRatioCharacter E)).subset (fun _ he => he.2.2.2))

theorem maskedEqualityCharacters_value_finite (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (hA : ∀ x ∈ A, equalityPatternCell E a r p x) :
    ∀ e ∈ maskedEqualityCharacters E a r p, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  rintro e ((he | he) | ⟨hs,hL,hR,rfl⟩)
  · exact maskedPolynomialCharacters_value_finite E.leftK a r p.2.1 A (fun x hx => (hA x hx).2.1) e he
  · exact maskedPolynomialCharacters_value_finite E.rightK a r p.2.2 A (fun x hx => (hA x hx).2.2) e he
  · apply rvMonomial_ratio_character_values_finite E.right E.left a r hR hL A
    intro x hx
    exact residue_ratio_of_equal_values _ _ (rvMonomial_rawEval_ne_zero E.left a r hL x) ((hA x hx).1.mpr hs)

/-- The actual total residue sums are residue-valued even off their
polynomial domain; guards still occur in the original formula. -/
theorem equality_total_value_split (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : Fin n → CanonicalRV.RVSort M)
    (hL : E.left.rawEval a r y ≠ 0) (hR : E.right.rawEval a r y ≠ 0) :
    E.left.rawEval a r y * E.leftK.rawEval a r y = E.right.rawEval a r y * E.rightK.rawEval a r y ↔
      if RVOperations.absoluteHom (E.left.rawEval a r y) = RVOperations.absoluteHom (E.right.rawEval a r y)
      then E.leftK.rawEval a r y = (E.right.rawEval a r y / E.left.rawEval a r y) * E.rightK.rawEval a r y
      else E.leftK.rawEval a r y = 0 ∧ E.rightK.rawEval a r y = 0 := by
  by_cases he : RVOperations.absoluteHom (E.left.rawEval a r y) = RVOperations.absoluteHom (E.right.rawEval a r y)
  · rw [if_pos he]
    exact residue_scaled_equality_ratio _ _ _ _ hL
  · rw [if_neg he]
    exact residue_scaled_equality_distinct_values _ _ _ _ hL hR (residueSum_inK_total _) (residueSum_inK_total _) he
end DiamondIntegral.Section3
