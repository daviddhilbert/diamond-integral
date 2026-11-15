import «section 5».ACFComplexRationalWitnesses
import «section 5».UniqueGraphSentences
import «section 5».RationalGraphFormulas
import «section 5».FiniteFormulaCovers

/-! A scalar complex-definable graph is covered by finitely many rational
graphs with original complex coefficients and nonzero denominators. The
same finite cover works in every elementary model of the complex field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
local instance rationalCoverCoefficientRing : CompatibleRing ℂ := compatibleRingOfRing ℂ
attribute [local instance] ComplexModels.ringStructure ComplexModels.acfModel ComplexModels.fieldModel
  ComplexModels.fieldStructure ComplexModels.compatibleRing ComplexModels.characteristicZero
  ComplexModels.algebraicallyClosed ComplexModels.algebra

theorem complex_graph_finite_rational_cover {n : ℕ}
    (φ : (Language.ring[[ℂ]]).Formula (Fin n ⊕ Fin 1))
    (hu : ∀ (x : Fin n → ℂ) (y z : ℂ), φ.Realize (Sum.elim x (fun _ => y)) →
      φ.Realize (Sum.elim x (fun _ => z)) → y = z) :
    ∃ s : Finset (MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ),
      ∀ (M : ComplexModels.Model) (x : Fin n → M) (y : M),
        φ.Realize (Sum.elim x (fun _ => y)) →
          ∃ pq ∈ s, (rationalGraphFormula pq.1 pq.2).Realize (Sum.elim x (fun _ => y)) := by
  have hcover (M : ComplexModels.Model) (v : Fin n ⊕ Fin 1 → M) (hφ : φ.Realize v) :
      ∃ pq : MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ,
        (rationalGraphFormula pq.1 pq.2).Realize v := by
    let x : Fin n → M := fun i => v (.inl i)
    let y := v (.inr 0)
    have hv : Sum.elim x (fun _ : Fin 1 => y) = v := by
      funext i
      cases i with
      | inl i => rfl
      | inr j => exact congrArg (fun k => v (.inr k)) (Subsingleton.elim 0 j)
    have hxy : φ.Realize (Sum.elim x (fun _ => y)) := by rw [hv]; exact hφ
    have hUnique (z : M) (hz : φ.Realize (Sum.elim x (fun _ => z))) : z = y :=
      complex_graph_unique_in_model φ hu M x z y hz hxy
    obtain ⟨p, q, hpq, hq⟩ := complex_model_graph_rational M φ x y hxy hUnique
    have hψ : (rationalGraphFormula p q).Realize (Sum.elim x (fun _ => y)) :=
      (rationalGraphFormula_realize p q M (ComplexModels.coefficientHom M)
        (ComplexModels.coefficientHom_constant M) x y).mpr ⟨hq, ((div_eq_iff hq).mp hpq).symm⟩
    exact ⟨(p, q), hv ▸ hψ⟩
  obtain ⟨s, hs⟩ := finite_formula_cover ComplexModels.theory φ
    (fun pq : MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ => rationalGraphFormula pq.1 pq.2) hcover
  exact ⟨s, fun M x y hxy => hs M (Sum.elim x (fun _ => y)) hxy⟩

theorem complex_scalar_graph_finite_rational_cover {n : ℕ}
    (φ : (Language.ring[[ℂ]]).Formula (Fin n ⊕ Fin 1))
    (hu : ∀ (x : Fin n → ℂ) (y z : ℂ), φ.Realize (Sum.elim x (fun _ => y)) →
      φ.Realize (Sum.elim x (fun _ => z)) → y = z) :
    ∃ s : Finset (MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ),
      ∀ (x : Fin n → ℂ) (y : ℂ), φ.Realize (Sum.elim x (fun _ => y)) →
        ∃ pq ∈ s, pq.2.eval₂ (RingHom.id ℂ) x ≠ 0 ∧
          y * pq.2.eval₂ (RingHom.id ℂ) x = pq.1.eval₂ (RingHom.id ℂ) x := by
  obtain ⟨s, hs⟩ := complex_graph_finite_rational_cover φ hu
  let M : ComplexModels.Model := Theory.ModelType.of ComplexModels.theory ℂ
  refine ⟨s, ?_⟩
  intro x y hxy
  obtain ⟨pq, hpq, hψ⟩ := hs M x y hxy
  refine ⟨pq, hpq, ?_⟩
  exact (rationalGraphFormula_realize pq.1 pq.2 ℂ (RingHom.id ℂ) (fun _ => rfl) x y).mp hψ

end DiamondIntegral.Section5
