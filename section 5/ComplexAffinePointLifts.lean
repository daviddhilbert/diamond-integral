import «section 5».InvariantConstructibleSubstrata
import «section 5».SchemeBranchPoints
import «section 5».ComplexConstructiblePoints

/-! A complex point in the scheme image of a finite-type complex
affine morphism lifts to an actual complex algebra point. Constructible
scheme subsets therefore inherit invariance proved on complex points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology TopologicalSpace
variable {S A : Type} [CommRing S] [CommRing A] [Algebra ℂ S] [Algebra ℂ A]

theorem complexAlgebraPoint_injective : Function.Injective (complexAlgebraPoint (A := S)) := by
  intro φ ψ he
  have hk := congrArg PrimeSpectrum.asIdeal he
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap ℂ S (φ x) ∈ (complexAlgebraPoint φ).asIdeal := by
    change φ (x - algebraMap ℂ S (φ x)) = 0
    simp
  rw [hk] at hx
  have hh : ψ (x - algebraMap ℂ S (φ x)) = 0 := hx
  have hval : ψ x - φ x = 0 := by simpa using hh
  exact (sub_eq_zero.mp hval).symm

theorem complexAlgebraPoint_comp (f : S →ₐ[ℂ] A) (φ : A →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom f.toRingHom) (complexAlgebraPoint φ) =
      complexAlgebraPoint (φ.comp f) := by
  apply PrimeSpectrum.ext
  rfl

theorem complexAlgebraPoint_closed (φ : S →ₐ[ℂ] ℂ) : IsClosed {complexAlgebraPoint φ} := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  exact RingHom.ker_isMaximal_of_surjective φ.toRingHom
    (fun c => ⟨algebraMap ℂ S c, by simp⟩)

theorem complex_point_mem_spec_image_iff [Algebra.FiniteType ℂ A]
    (f : S →ₐ[ℂ] A) (φ : S →ₐ[ℂ] ℂ) :
    complexAlgebraPoint φ ∈ Set.range (Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
      ∃ ψ : A →ₐ[ℂ] ℂ, ψ.comp f = φ := by
  constructor
  · rintro ⟨x, hx⟩
    let F := Spec.map (CommRingCat.ofHom f.toRingHom)
    let Z := F ⁻¹' {complexAlgebraPoint φ}
    have hZ : IsClosed Z := (complexAlgebraPoint_closed φ).preimage F.continuous
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
    obtain ⟨ψ, hψ⟩ := constructible_complex_point Z
      (locallyClosed_constructible_of_noetherian hZ.isLocallyClosed) ⟨x, hx⟩
    refine ⟨ψ, complexAlgebraPoint_injective ?_⟩
    exact (complexAlgebraPoint_comp f ψ).symm.trans hψ
  · rintro ⟨ψ, hψ⟩
    refine ⟨complexAlgebraPoint ψ, ?_⟩
    rw [complexAlgebraPoint_comp, hψ]

theorem constructible_invariant_of_complex_points [Algebra.FiniteType ℂ S]
    (U : Set (PrimeSpectrum S)) (hU : IsConstructible U) (k : S →ₐ[ℂ] S)
    (hpoint : ∀ φ : S →ₐ[ℂ] ℂ,
      complexAlgebraPoint (φ.comp k) ∈ U ↔ complexAlgebraPoint φ ∈ U) :
    ∀ x, Spec.map (CommRingCat.ofHom k.toRingHom) x ∈ U ↔ x ∈ U := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  letI : NoetherianSpace (Spec (.of S)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum S))
  let F := Spec.map (CommRingCat.ofHom k.toRingHom)
  have hpre : IsConstructible (F ⁻¹' U) :=
    hU.preimage F.continuous (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _)
  have he : F ⁻¹' U = U := constructible_eq_of_complex_points _ _ hpre hU (by
    intro φ
    change F (complexAlgebraPoint φ) ∈ U ↔ complexAlgebraPoint φ ∈ U
    rw [complexAlgebraPoint_comp]
    exact hpoint φ)
  intro x
  exact Set.ext_iff.mp he x

end DiamondIntegral.Section5
