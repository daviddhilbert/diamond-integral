import «section 5».ConstructibleSpectrumObjects

/-! Complex points lift through actual constructible images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology TopologicalSpace
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

theorem complex_point_lift_constructible_image [Algebra.FiniteType ℂ B]
    (f : A →ₐ[ℂ] B) (U : Set (PrimeSpectrum B)) (hU : IsConstructible U)
    (φ : A →ₐ[ℂ] ℂ)
    (hφ : complexAlgebraPoint φ ∈ Spec.map (CommRingCat.ofHom f.toRingHom) '' U) :
    ∃ ψ : B →ₐ[ℂ] ℂ, complexAlgebraPoint ψ ∈ U ∧ ψ.comp f = φ := by
  obtain ⟨p, hp, hpf⟩ := hφ
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  letI : NoetherianSpace (Spec (.of B)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum B))
  let Z := Spec.map (CommRingCat.ofHom f.toRingHom) ⁻¹' {complexAlgebraPoint φ}
  have hZ : IsClosed Z := (complexAlgebraPoint_closed φ).preimage
    (Spec.map (CommRingCat.ofHom f.toRingHom)).continuous
  obtain ⟨ψ, hψ⟩ := constructible_complex_point (U ∩ Z)
    (hU.inter (locallyClosed_constructible_of_noetherian hZ.isLocallyClosed)) ⟨p, hp, hpf⟩
  refine ⟨ψ, hψ.1, complexAlgebraPoint_injective ?_⟩
  exact (complexAlgebraPoint_comp f ψ).symm.trans hψ.2

theorem complexTupleSpectrumPoint_injective {α : Type} :
    Function.Injective (complexTupleSpectrumPoint : (α → ℂ) → _) := by
  intro x y he
  funext i
  have hx : MvPolynomial.X i - MvPolynomial.C (x i) ∈ (complexTupleSpectrumPoint x).asIdeal := by
    change (MvPolynomial.eval₂Hom (RingHom.id ℂ) x) (MvPolynomial.X i - MvPolynomial.C (x i)) = 0
    simp
  rw [he] at hx
  have hh : y i - x i = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id ℂ) y) (MvPolynomial.X i - MvPolynomial.C (x i)) = 0 at hx
    simpa using hx
  exact (sub_eq_zero.mp hh).symm

end DiamondIntegral.Section5
