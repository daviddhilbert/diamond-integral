import «section 5».ComplexPointsSeparate
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Vanishing at all complex points detects nilpotence even before
reduction. Such elements vanish under every map to a reduced ring. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem complex_points_nilpotent (a : A) (ha : ∀ φ : A →ₐ[ℂ] ℂ, φ a = 0) : IsNilpotent a := by
  let I : Ideal A := (⊥ : Ideal A).radical
  letI : IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp (Ideal.radical_isRadical _)
  have hz : Ideal.Quotient.mk I a = 0 := complex_points_separate_zero _
    (fun φ => ha (φ.comp (Ideal.Quotient.mkₐ ℂ I)))
  have hmem : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, Ideal.mem_bot.mp hk⟩

theorem complex_points_zero_under_reduced_map {R : Type*} [CommRing R] [IsReduced R]
    (f : A →+* R) (a : A) (ha : ∀ φ : A →ₐ[ℂ] ℂ, φ a = 0) : f a = 0 :=
  ((complex_points_nilpotent a ha).map f).eq_zero

theorem complex_points_maps_agree_after_reduction {B R : Type*}
    [CommRing B] [Algebra ℂ B] [CommRing R] [Algebra ℂ R] [IsReduced R]
    (f g : B →ₐ[ℂ] A) (h : ∀ φ : A →ₐ[ℂ] ℂ, φ.comp f = φ.comp g)
    (r : A →ₐ[ℂ] R) : r.comp f = r.comp g := by
  ext b
  have hz := complex_points_zero_under_reduced_map r.toRingHom (f b - g b)
    (fun φ => by
      have he : φ (f b) = φ (g b) := AlgHom.congr_fun (h φ) b
      rw [map_sub, he, sub_self])
  have he : r (f b) - r (g b) = 0 := by
    change r.toRingHom (f b) - r.toRingHom (g b) = 0
    rw [← map_sub]
    exact hz
  exact sub_eq_zero.mp he

end DiamondIntegral.Section5
