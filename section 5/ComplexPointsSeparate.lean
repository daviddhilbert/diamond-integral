import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Complex points separate elements and algebra maps of reduced
finite-type complex algebras. This proves the point-to-scheme equality
criterion needed for the regular inverse constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [IsReduced A]

theorem complex_points_separate_zero (a : A)
    (ha : ∀ φ : A →ₐ[ℂ] ℂ, φ a = 0) : a = 0 := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℂ A)
  obtain ⟨p, hp⟩ := hf a
  have hrad : p ∈ (RingHom.ker f.toRingHom).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
      (K := ℂ) (RingHom.ker f.toRingHom)]
    intro x hx
    let φ : A →ₐ[ℂ] ℂ := AlgHom.liftOfSurjective f hf (MvPolynomial.aeval x)
      (fun q hq => hx q hq)
    have h := ha φ
    rw [← hp] at h
    exact (AlgHom.liftOfSurjective_apply f hf _ _ p).symm.trans h
  obtain ⟨k, hk⟩ := hrad
  have hnil : IsNilpotent a := by
    refine ⟨k, ?_⟩
    rw [← hp, ← map_pow]
    exact hk
  exact hnil.eq_zero

theorem complex_points_separate (a b : A)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, φ a = φ b) : a = b := by
  apply sub_eq_zero.mp
  exact complex_points_separate_zero (a - b) (fun φ => by rw [map_sub, h φ, sub_self])

theorem complex_points_algHom_ext {B : Type*} [CommRing B] [Algebra ℂ B]
    (f g : B →ₐ[ℂ] A) (h : ∀ φ : A →ₐ[ℂ] ℂ, φ.comp f = φ.comp g) : f = g := by
  ext b
  exact complex_points_separate (f b) (g b) (fun φ => AlgHom.congr_fun (h φ) b)

theorem complex_points_ideal_le_ker {B : Type*} [CommRing B] [Algebra ℂ B]
    (f : B →ₐ[ℂ] A) (J : Ideal B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, J ≤ RingHom.ker (φ.comp f).toRingHom) :
    J ≤ RingHom.ker f.toRingHom := by
  intro b hb
  exact complex_points_separate_zero (f b) (fun φ => h φ hb)

def complexPointQuotientLift {B : Type*} [CommRing B] [Algebra ℂ B]
    (f : B →ₐ[ℂ] A) (J : Ideal B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, J ≤ RingHom.ker (φ.comp f).toRingHom) :
    B ⧸ J →ₐ[ℂ] A := Ideal.Quotient.liftₐ J f (complex_points_ideal_le_ker f J h)

theorem complexPointQuotientLift_mk {B : Type*} [CommRing B] [Algebra ℂ B]
    (f : B →ₐ[ℂ] A) (J : Ideal B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, J ≤ RingHom.ker (φ.comp f).toRingHom) (b : B) :
    complexPointQuotientLift f J h (Ideal.Quotient.mk J b) = f b := rfl

def complexPointInverseEquiv {B : Type*} [CommRing B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] [IsReduced B] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] A)
    (hfg : ∀ φ : B →ₐ[ℂ] ℂ, φ.comp (f.comp g) = φ)
    (hgf : ∀ φ : A →ₐ[ℂ] ℂ, φ.comp (g.comp f) = φ) : A ≃ₐ[ℂ] B :=
  AlgEquiv.ofAlgHom f g
    (complex_points_algHom_ext _ _ (fun φ => by simpa using hfg φ))
    (complex_points_algHom_ext _ _ (fun φ => by simpa using hgf φ))

end DiamondIntegral.Section5
