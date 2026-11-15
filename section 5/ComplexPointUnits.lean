import «section 5».ComplexConstructiblePoints

/-! Nonvanishing at every complex point detects units in any finite-type
complex algebra, including nonreduced and zero algebras. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem complex_points_isUnit (a : A) :
    IsUnit a ↔ ∀ φ : A →ₐ[ℂ] ℂ, φ a ≠ 0 := by
  constructor
  · intro ha φ
    exact isUnit_iff_ne_zero.mp (ha.map φ.toRingHom)
  · intro ha
    by_contra hn
    have hI : Ideal.span ({a} : Set A) ≠ ⊤ := by
      intro htop
      exact hn (Ideal.span_singleton_eq_top.mp htop)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
    let D : PrimeSpectrum.BasicConstructibleSetData A := ⟨1, 1, fun _ => a⟩
    have hne : D.toSet.Nonempty := by
      refine ⟨⟨m, hm.isPrime⟩, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        exact hle (Ideal.subset_span (Set.mem_singleton a))
      · intro h
        exact hm.isPrime.one_notMem (h (Set.mem_singleton 1))
    obtain ⟨φ, hφ⟩ := basic_constructible_complex_point D hne
    exact ha φ (hφ.1 ⟨0, rfl⟩)

end DiamondIntegral.Section5
