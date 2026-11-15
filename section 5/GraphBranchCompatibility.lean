import «section 5».ConstructibleBijectionPieces
import «section 5».ReducedAffineBranchGluing

/-! Single-valuedness of the original complex graph proves the
overlap compatibility of its actual affine graph schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {n m : ℕ}

theorem basicGraphPoint_mem
    (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (φ : BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ) :
    complexTupleSpectrumPoint (Sum.elim
      (fun i => φ (basicGraphLeft D (MvPolynomial.X i)))
      (fun j => φ (basicGraphRight D (MvPolynomial.X j)))) ∈ D.toSet := by
  have he : Sum.elim (fun i => φ (basicGraphLeft D (MvPolynomial.X i)))
      (fun j => φ (basicGraphRight D (MvPolynomial.X j))) =
      fun k => (φ.comp (basicConstructibleCoordinateMap D)) (MvPolynomial.X k) := by
    funext k
    cases k <;> simp [basicGraphLeft, basicGraphRight]
  rw [he, complexTupleSpectrumPoint_algHom]
  exact basicConstructiblePoint_mem D φ

theorem graph_branches_complex_compatible {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z) :
    ∀ i j (φ : BasicConstructibleCoordinateRing (D i) →ₐ[ℂ] ℂ)
      (ψ : BasicConstructibleCoordinateRing (D j) →ₐ[ℂ] ℂ),
      φ.comp (basicGraphLeft (D i)) = ψ.comp (basicGraphLeft (D j)) →
        φ.comp (basicGraphRight (D i)) = ψ.comp (basicGraphRight (D j)) := by
  intro i j φ ψ he
  have hx : (fun k => φ (basicGraphLeft (D i) (MvPolynomial.X k))) =
      (fun k => ψ (basicGraphLeft (D j) (MvPolynomial.X k))) := by
    funext k
    exact AlgHom.congr_fun he (MvPolynomial.X k)
  have hi := hD i _ (basicGraphPoint_mem (D i) φ)
  have hj := hD j _ (basicGraphPoint_mem (D j) ψ)
  rw [← hx] at hj
  have hy := hu _ _ _ hi hj
  apply MvPolynomial.algHom_ext
  intro k
  exact congrFun hy k

theorem graph_branches_inverse_complex_compatible {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hD : ∀ j v, complexTupleSpectrumPoint v ∈ (D j).toSet → v ∈ G)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z) :
    ∀ i j (φ : BasicConstructibleCoordinateRing (D i) →ₐ[ℂ] ℂ)
      (ψ : BasicConstructibleCoordinateRing (D j) →ₐ[ℂ] ℂ),
      φ.comp (basicGraphRight (D i)) = ψ.comp (basicGraphRight (D j)) →
        φ.comp (basicGraphLeft (D i)) = ψ.comp (basicGraphLeft (D j)) := by
  intro i j φ ψ he
  have hy : (fun k => φ (basicGraphRight (D i) (MvPolynomial.X k))) =
      (fun k => ψ (basicGraphRight (D j) (MvPolynomial.X k))) := by
    funext k
    exact AlgHom.congr_fun he (MvPolynomial.X k)
  have hi := hD i _ (basicGraphPoint_mem (D i) φ)
  have hj := hD j _ (basicGraphPoint_mem (D j) ψ)
  rw [← hy] at hj
  have hx := hv _ _ _ hi hj
  apply MvPolynomial.algHom_ext
  intro k
  exact congrFun hx k

end DiamondIntegral.Section5
