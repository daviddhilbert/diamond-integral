import «section 5».ComplexAffinePointLifts
import «section 5».GraphBranchCompatibility
import «section 5».BasicConstructiblePoints

/-! The source scheme image of the finite affine graph pieces has
exactly the existential projection of the original complex graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] basicConstructibleCoordinate_finiteType

theorem basicGraphLeft_complex_image_iff {n m : ℕ} {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : ∀ v, v ∈ G ↔ ∃ j, complexTupleSpectrumPoint v ∈ (D j).toSet)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    complexAlgebraPoint φ ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphLeft (D j)).toRingHom))) ↔
      ∃ y : Fin m → ℂ, Sum.elim (fun i => φ (MvPolynomial.X i)) y ∈ G := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ψ, hψ⟩ := (complex_point_mem_spec_image_iff (basicGraphLeft (D j)) φ).mp hj
    refine ⟨(fun i => ψ (basicGraphRight (D j) (MvPolynomial.X i))), ?_⟩
    have hg := (hG _).mpr ⟨j, basicGraphPoint_mem (D j) ψ⟩
    have he : (fun i => ψ (basicGraphLeft (D j) (MvPolynomial.X i))) =
        (fun i => φ (MvPolynomial.X i)) := by
      funext i
      exact AlgHom.congr_fun hψ (MvPolynomial.X i)
    rwa [he] at hg
  · rintro ⟨y, hy⟩
    obtain ⟨j, hj⟩ := (hG _).mp hy
    let ψ : MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] ℂ :=
      MvPolynomial.aeval (Sum.elim (fun i => φ (MvPolynomial.X i)) y)
    have hp : complexAlgebraPoint ψ =
        complexTupleSpectrumPoint (Sum.elim (fun i => φ (MvPolynomial.X i)) y) := by
      apply PrimeSpectrum.ext
      rfl
    have hψ : complexAlgebraPoint ψ ∈ (D j).toSet := hp.symm ▸ hj
    let θ := basicConstructiblePointLift (D j) ψ hψ
    apply Set.mem_iUnion.mpr
    refine ⟨j, (complex_point_mem_spec_image_iff (basicGraphLeft (D j)) φ).mpr ⟨θ, ?_⟩⟩
    apply MvPolynomial.algHom_ext
    intro i
    have he := AlgHom.congr_fun (basicConstructiblePointLift_coordinateMap (D j) ψ hψ)
      (MvPolynomial.X (.inl i))
    simpa [θ, basicGraphLeft, ψ] using he

theorem basicGraphRight_complex_image_iff {n m : ℕ} {J : Type}
    (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : ∀ v, v ∈ G ↔ ∃ j, complexTupleSpectrumPoint v ∈ (D j).toSet)
    (φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ) :
    complexAlgebraPoint φ ∈
      (⋃ j, Set.range (Spec.map (CommRingCat.ofHom (basicGraphRight (D j)).toRingHom))) ↔
      ∃ x : Fin n → ℂ, Sum.elim x (fun i => φ (MvPolynomial.X i)) ∈ G := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ψ, hψ⟩ := (complex_point_mem_spec_image_iff (basicGraphRight (D j)) φ).mp hj
    refine ⟨(fun i => ψ (basicGraphLeft (D j) (MvPolynomial.X i))), ?_⟩
    have hg := (hG _).mpr ⟨j, basicGraphPoint_mem (D j) ψ⟩
    have he : (fun i => ψ (basicGraphRight (D j) (MvPolynomial.X i))) =
        (fun i => φ (MvPolynomial.X i)) := by
      funext i
      exact AlgHom.congr_fun hψ (MvPolynomial.X i)
    rwa [he] at hg
  · rintro ⟨x, hx⟩
    obtain ⟨j, hj⟩ := (hG _).mp hx
    let ψ : MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] ℂ :=
      MvPolynomial.aeval (Sum.elim x (fun i => φ (MvPolynomial.X i)))
    have hp : complexAlgebraPoint ψ =
        complexTupleSpectrumPoint (Sum.elim x (fun i => φ (MvPolynomial.X i))) := by
      apply PrimeSpectrum.ext
      rfl
    have hψ : complexAlgebraPoint ψ ∈ (D j).toSet := hp.symm ▸ hj
    let θ := basicConstructiblePointLift (D j) ψ hψ
    apply Set.mem_iUnion.mpr
    refine ⟨j, (complex_point_mem_spec_image_iff (basicGraphRight (D j)) φ).mpr ⟨θ, ?_⟩⟩
    apply MvPolynomial.algHom_ext
    intro i
    have he := AlgHom.congr_fun (basicConstructiblePointLift_coordinateMap (D j) ψ hψ)
      (MvPolynomial.X (.inr i))
    simpa [θ, basicGraphRight, ψ] using he

end DiamondIntegral.Section5
