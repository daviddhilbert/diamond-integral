import «section 5».ComplexPointsSeparate
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Every nonempty constructible subset of a finite-type complex
affine scheme contains an actual complex point. Consequently complex
points determine constructible scheme subsets, including all generic
points in the resulting set identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology
variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

def complexAlgebraPoint (φ : A →ₐ[ℂ] ℂ) : PrimeSpectrum A :=
  ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩

theorem basic_constructible_complex_point (D : PrimeSpectrum.BasicConstructibleSetData A)
    (hne : D.toSet.Nonempty) : ∃ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint φ ∈ D.toSet := by
  obtain ⟨x, hx⟩ := hne
  let I : Ideal A := Ideal.span (Set.range D.g)
  let J := I.radical
  have hg (i : Fin D.n) : D.g i ∈ x.asIdeal := hx.1 ⟨i, rfl⟩
  have hf : D.f ∉ x.asIdeal := by
    simpa [PrimeSpectrum.mem_zeroLocus] using hx.2
  have hI : I ≤ x.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg i)
  have hJ : J ≤ x.asIdeal := (Ideal.radical_mono hI).trans_eq x.isPrime.isRadical.radical
  letI : IsReduced (A ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp I.radical_isRadical
  have hn : Ideal.Quotient.mk J D.f ≠ 0 := by
    intro h
    exact hf (hJ (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hex : ∃ φ : (A ⧸ J) →ₐ[ℂ] ℂ, φ (Ideal.Quotient.mk J D.f) ≠ 0 := by
    by_contra! h
    exact hn (complex_points_separate_zero _ h)
  obtain ⟨φ, hφ⟩ := hex
  let ψ : A →ₐ[ℂ] ℂ := φ.comp (Ideal.Quotient.mkₐ ℂ J)
  refine ⟨ψ, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := ha
    change φ (Ideal.Quotient.mk J (D.g i)) = 0
    have hmem : D.g i ∈ J := Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  · simpa [PrimeSpectrum.mem_zeroLocus, complexAlgebraPoint, RingHom.mem_ker, ψ] using hφ

theorem constructible_complex_point (D : Set (PrimeSpectrum A)) (hD : IsConstructible D)
    (hne : D.Nonempty) : ∃ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint φ ∈ D := by
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hD
  obtain ⟨x, hx⟩ := hne
  obtain ⟨d, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hd, hxd⟩ := Set.mem_iUnion.mp hx
  obtain ⟨φ, hφ⟩ := basic_constructible_complex_point d ⟨x, hxd⟩
  exact ⟨φ, Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, hφ⟩⟩⟩

theorem constructible_eq_of_complex_points (D E : Set (PrimeSpectrum A))
    (hD : IsConstructible D) (hE : IsConstructible E)
    (he : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint φ ∈ D ↔ complexAlgebraPoint φ ∈ E) : D = E := by
  have hsub (S T : Set (PrimeSpectrum A)) (hS : IsConstructible S) (hT : IsConstructible T)
      (hst : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint φ ∈ S → complexAlgebraPoint φ ∈ T) : S ⊆ T := by
    intro x hx
    by_contra hn
    obtain ⟨φ, hφ⟩ := constructible_complex_point (S \ T) (hS.sdiff hT) ⟨x, hx, hn⟩
    exact hφ.2 (hst φ hφ.1)
  exact Set.Subset.antisymm (hsub D E hD hE (fun φ => (he φ).mp))
    (hsub E D hE hD (fun φ => (he φ).mpr))

end DiamondIntegral.Section5
