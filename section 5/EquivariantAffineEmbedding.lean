import «section 5».EquivariantAlgebraGenerators
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! An actual equivariant closed affine embedding for every finite-type
complex algebra with finite cyclic action. Equivariance is the full
coordinate-algebra square, and the induced Spec morphism is a checked
closed immersion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry

def polynomialDiagonalAction {n : ℕ} (w : Fin n → ℤ) (ζ : ℂˣ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C ((ζ ^ w i : ℂˣ) : ℂ) * MvPolynomial.X i)

theorem polynomialDiagonalAction_one {n : ℕ} (w : Fin n → ℤ) :
    polynomialDiagonalAction w 1 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialDiagonalAction]

theorem polynomialDiagonalAction_mul {n : ℕ} (w : Fin n → ℤ) (ζ ξ : ℂˣ) :
    polynomialDiagonalAction w (ζ * ξ) = (polynomialDiagonalAction w ζ).comp (polynomialDiagonalAction w ξ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialDiagonalAction, mul_zpow, mul_comm, mul_left_comm, mul_assoc]

theorem finite_cyclic_equivariant_affine_embedding {A : Type} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* (A ≃ₐ[ℂ] A)) :
    ∃ n : ℕ, ∃ x : Fin n → A, ∃ w : Fin n → ℤ,
      IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A).toRingHom)) ∧
        ∀ ζ : rootsOfUnity (N : ℕ) ℂ,
          (ρ ζ).toAlgHom.comp (MvPolynomial.aeval x) =
            (MvPolynomial.aeval x).comp (polynomialDiagonalAction w ζ.val) := by
  obtain ⟨n, x, w, hs, hw⟩ := finite_cyclic_eigen_generators N ρ
  refine ⟨n, x, w, IsClosedImmersion.spec_of_surjective _ hs, ?_⟩
  intro ζ
  apply MvPolynomial.algHom_ext
  intro i
  simpa [polynomialDiagonalAction, Algebra.smul_def] using hw ζ i

end DiamondIntegral.Section5
