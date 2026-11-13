import «section 3».MaskedEqualityCharacters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}


/-- On one outer-value cell, a guarded equality depends only on its
active residue characters and on the coordinate Gamma values. -/
theorem equality_payload_depends_on_masked_characters (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ maskedEqualityCharacters E a r p, integerCharacter e x = integerCharacter e y)
    (hvalues : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i))
    (hpattern : equalityPatternCell E a r p x) :
    (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) * E.leftK.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) =
      E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) * E.rightK.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) ↔
    (E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M)) * E.leftK.rawEval a r (fun i => (y i : CanonicalRV.RVSort M)) =
      E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M)) * E.rightK.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) := by
  have hKL := maskedPolynomial_depends_on_characters E.leftK a r p.2.1 x y hpattern.2.1 hvalues
    (fun e he => hxy e (Or.inl (Or.inl he)))
  have hKR := maskedPolynomial_depends_on_characters E.rightK a r p.2.2 x y hpattern.2.2 hvalues
    (fun e he => hxy e (Or.inl (Or.inr he)))
  by_cases hL : rvMonomialCoefficient E.left a r = 0
  · rw [rvMonomial_zero_coefficient E.left a r hL,rvMonomial_zero_coefficient E.left a r hL,zero_mul,zero_mul]
    by_cases hR : rvMonomialCoefficient E.right a r = 0
    · rw [rvMonomial_zero_coefficient E.right a r hR,rvMonomial_zero_coefficient E.right a r hR,zero_mul,zero_mul]
    · have hnX := rvMonomial_rawEval_ne_zero E.right a r hR x
      have hnY := rvMonomial_rawEval_ne_zero E.right a r hR y
      have hz (u k : CanonicalRV.RVSort M) (hu : u ≠ 0) : 0 = u * k ↔ k = 0 :=
        ⟨fun h => (mul_eq_zero.mp h.symm).resolve_left hu,fun h => by rw [h,mul_zero]⟩
      rw [hz _ _ hnX,hz _ _ hnY,hKR]
  · by_cases hR : rvMonomialCoefficient E.right a r = 0
    · rw [rvMonomial_zero_coefficient E.right a r hR,rvMonomial_zero_coefficient E.right a r hR,zero_mul,zero_mul]
      simp only [mul_eq_zero,rvMonomial_rawEval_ne_zero E.left a r hL x,
        rvMonomial_rawEval_ne_zero E.left a r hL y,false_or,hKL]
    · have hLX := rvMonomial_rawEval_ne_zero E.left a r hL x
      have hLY := rvMonomial_rawEval_ne_zero E.left a r hL y
      have hRX := rvMonomial_rawEval_ne_zero E.right a r hR x
      have hRY := rvMonomial_rawEval_ne_zero E.right a r hR y
      rw [equality_total_value_split E a r _ hLX hRX,
        equality_total_value_split E a r _ hLY hRY]
      have hlv := rvMonomial_absolute_depends_on_values E.left a r x y hvalues
      have hrv := rvMonomial_absolute_depends_on_values E.right a r x y hvalues
      by_cases he : RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
          RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))
      · have heY : RVOperations.absoluteHom (E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) =
            RVOperations.absoluteHom (E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) :=
          hlv.symm.trans (he.trans hrv)
        have hs : p.1 = true := hpattern.1.mp he
        have hc := hxy (equalityRatioCharacter E) (Or.inr ⟨hs,hL,hR,rfl⟩)
        change integerCharacter (fun i => E.right.powers i - E.left.powers i) x =
          integerCharacter (fun i => E.right.powers i - E.left.powers i) y at hc
        have hr : E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) /
            E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) =
            E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M)) /
            E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M)) := by
          rw [rvMonomial_ratio_units,rvMonomial_ratio_units,hc]
        rw [if_pos he,if_pos heY,hKL,hKR,hr]
      · have heY : RVOperations.absoluteHom (E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) ≠
            RVOperations.absoluteHom (E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))) :=
          fun hh => he (hlv.trans (hh.trans hrv.symm))
        rw [if_neg he,if_neg heY,hKL,hKR]
end DiamondIntegral.Section3
