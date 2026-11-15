import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations

/-! Prime avoidance puts every finite subset of an open affine-spectrum
locus in one principal open contained in that locus. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical TopologicalSpace

theorem finite_points_principal_neighborhood {A : Type*} [CommRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U)
    (T : Set (PrimeSpectrum A)) (hT : T.Finite) (hTU : T ⊆ U) :
    ∃ f : A, T ⊆ PrimeSpectrum.basicOpen f ∧ (PrimeSpectrum.basicOpen f : Set _) ⊆ U := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨p₀, hp₀⟩ := hne
  let I := PrimeSpectrum.vanishingIdeal Uᶜ
  have hI : PrimeSpectrum.zeroLocus (I : Set A) = Uᶜ := by
    exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Uᶜ).trans hU.isClosed_compl.closure_eq
  have hn : ¬∃ p ∈ T, I ≤ p.asIdeal := by
    rintro ⟨p, hp, hIp⟩
    have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set A) := hIp
    rw [hI] at hz
    exact hz (hTU hp)
  have hnot : ¬ (I : Set A) ⊆ ⋃ p ∈ T, (p.asIdeal : Set A) := by
    intro h
    exact hn ((Ideal.subset_union_prime_finite hT p₀ p₀ (fun p _ _ _ => p.isPrime)).mp h)
  obtain ⟨f, hf, hnf⟩ := Set.not_subset.mp hnot
  refine ⟨f, ?_, ?_⟩
  · intro p hp
    change f ∉ p.asIdeal
    intro hfp
    exact hnf (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hfp⟩⟩)
  · intro p hp
    by_contra hnU
    have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set A) := by rwa [hI]
    exact hp (hz hf)

end DiamondIntegral.Section5
