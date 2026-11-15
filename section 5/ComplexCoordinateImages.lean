import «section 5».ComplexConstructibleImages

/-! Constructible coordinate projections lift complex tuples to actual
complex tuples in the original constructible spectrum locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology

theorem complex_coordinate_lift {n k : ℕ} (f : Fin k → Fin n)
    (U : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (hU : IsConstructible U) (x : Fin k → ℂ)
    (hx : complexTupleSpectrumPoint x ∈ Spec.map (CommRingCat.ofHom
      (MvPolynomial.rename (R := ℂ) f).toRingHom) '' U) :
    ∃ z : Fin n → ℂ, complexTupleSpectrumPoint z ∈ U ∧ z ∘ f = x := by
  let φ : MvPolynomial (Fin k) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hp : complexTupleSpectrumPoint x = complexAlgebraPoint φ := by
    simpa only [φ, MvPolynomial.aeval_X] using complexTupleSpectrumPoint_algHom φ
  obtain ⟨ψ, hψ, he⟩ := complex_point_lift_constructible_image (MvPolynomial.rename f) U hU φ (hp ▸ hx)
  refine ⟨fun i => ψ (MvPolynomial.X i), (complexTupleSpectrumPoint_algHom ψ).symm ▸ hψ, ?_⟩
  funext i
  have hh := AlgHom.congr_fun he (MvPolynomial.X i)
  simpa only [Function.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, φ, MvPolynomial.aeval_X] using hh

end DiamondIntegral.Section5
