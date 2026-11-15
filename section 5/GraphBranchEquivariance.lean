import «section 5».GraphBranchCompatibility
import «section 5».EquivariantBranchGluing

/-! The transformed branch compatibility needed for equivariant
gluing follows from invariance of the original complex graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

theorem graph_branches_transformed_complex_compatible {n m : ℕ} {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (k : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ)
    (l : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ)
    (hInv : ∀ (x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ)
      (y : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ),
      Sum.elim (fun i => x (MvPolynomial.X i)) (fun j => y (MvPolynomial.X j)) ∈ G →
      Sum.elim (fun i => (x.comp k) (MvPolynomial.X i))
        (fun j => (y.comp l) (MvPolynomial.X j)) ∈ G) :
    ∀ i j (φ : BasicConstructibleCoordinateRing (D i) →ₐ[ℂ] ℂ)
      (ψ : BasicConstructibleCoordinateRing (D j) →ₐ[ℂ] ℂ),
      φ.comp ((basicGraphLeft (D i)).comp k) = ψ.comp (basicGraphLeft (D j)) →
        φ.comp ((basicGraphRight (D i)).comp l) = ψ.comp (basicGraphRight (D j)) := by
  intro i j φ ψ he
  have hi := hInv (φ.comp (basicGraphLeft (D i))) (φ.comp (basicGraphRight (D i)))
    (hD i _ (basicGraphPoint_mem (D i) φ))
  have hj := hD j _ (basicGraphPoint_mem (D j) ψ)
  have hx : (fun t => ((φ.comp (basicGraphLeft (D i))).comp k) (MvPolynomial.X t)) =
      (fun t => ψ (basicGraphLeft (D j) (MvPolynomial.X t))) := by
    funext t
    exact AlgHom.congr_fun he (MvPolynomial.X t)
  rw [hx] at hi
  have hy := hu _ _ _ hi hj
  apply MvPolynomial.algHom_ext
  intro t
  exact congrFun hy t

theorem graph_branches_inverse_transformed_complex_compatible {n m : ℕ} {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z)
    (k : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ)
    (l : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ)
    (hInv : ∀ (x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ)
      (y : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ),
      Sum.elim (fun i => x (MvPolynomial.X i)) (fun j => y (MvPolynomial.X j)) ∈ G →
      Sum.elim (fun i => (x.comp k) (MvPolynomial.X i))
        (fun j => (y.comp l) (MvPolynomial.X j)) ∈ G) :
    ∀ i j (φ : BasicConstructibleCoordinateRing (D i) →ₐ[ℂ] ℂ)
      (ψ : BasicConstructibleCoordinateRing (D j) →ₐ[ℂ] ℂ),
      φ.comp ((basicGraphRight (D i)).comp l) = ψ.comp (basicGraphRight (D j)) →
        φ.comp ((basicGraphLeft (D i)).comp k) = ψ.comp (basicGraphLeft (D j)) := by
  intro i j φ ψ he
  have hi := hInv (φ.comp (basicGraphLeft (D i))) (φ.comp (basicGraphRight (D i)))
    (hD i _ (basicGraphPoint_mem (D i) φ))
  have hj := hD j _ (basicGraphPoint_mem (D j) ψ)
  have hy : (fun t => ((φ.comp (basicGraphRight (D i))).comp l) (MvPolynomial.X t)) =
      (fun t => ψ (basicGraphRight (D j) (MvPolynomial.X t))) := by
    funext t
    exact AlgHom.congr_fun he (MvPolynomial.X t)
  rw [hy] at hi
  have hx := hv _ _ _ hi hj
  apply MvPolynomial.algHom_ext
  intro t
  exact congrFun hx t

end DiamondIntegral.Section5
