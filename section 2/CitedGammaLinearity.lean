import «section 2».GammaAffineBounds
import «section 2».AtomicBaseChange
import Section4.GammaPredicates

/-! Replaceable value-group background for 2.41. The proof of [18,
Lemma 3.18] explicitly uses quantifier elimination and piecewise linearity
of definable Gamma functions (arXiv:0809.0473v2, proof of Lemma 3.18).
This input records only that unary Gamma background, not the RV-domain
bounded-image assertion or its higher-dimensional induction. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite cover by rational-affine laws, written without choosing RV
representatives of the actual Gamma coefficients or input/output values.
The source's standing characteristic and ground-value-group hypotheses
are retained explicitly. -/
def GammaPiecewiseRationalAffineInput : Prop :=
  M ⊨ Axioms.ACVF00 → ∀ S : Set M,
    NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M) →
    ∀ (D : Set (Gamma M)) (f : Gamma M → Gamma M),
      GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1) →
      ∃ (k : ℕ) (p : Fin k → ℤ) (q : Fin k → ℕ) (c : Fin k → Gamma M),
        (∀ i, q i ≠ 0) ∧ ∀ x ∈ D, ∃ i, f x ^ q i = c i * x ^ p i

theorem gamma_definable_image_doubly_bounded
    (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    (S : Set M) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Gamma M)) (f : Gamma M → Gamma M)
    (hf : GammaSyntax.Definable S (fun z : Fin 2 → Gamma M => z 0 ∈ D ∧ f (z 0) = z 1))
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ D, γ⁻¹ ≤ x ∧ x ≤ γ) :
    ∃ γ : Gamma M, ∀ y ∈ f '' D, γ⁻¹ ≤ y ∧ y ≤ γ := by
  obtain ⟨k,p,q,c,hq,hcover⟩ := linear h00 S hΓ D f hf
  exact gamma_finite_power_laws_bounded D ((gamma_symmetric_bound_iff D).mp hbounded) f p q hq c hcover

end DiamondIntegral.Section2
