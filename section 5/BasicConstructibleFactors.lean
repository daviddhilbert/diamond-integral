import «section 5».BasicConstructiblePoints
import «section 5».ComplexPointUnits

/-! Actual factorization through reduced basic constructible schemes
from the complex-point condition. The source is reduced and of finite
type; no scheme factorization is assumed as an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable [Algebra.FiniteType ℂ A] [IsReduced A]

theorem complexPointBasicFactor_kernel (f : B →ₐ[ℂ] A)
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint (φ.comp f) ∈ D.toSet) :
    basicConstructibleIdeal D ≤ RingHom.ker f.toRingHom :=
  complex_points_ideal_le_ker f _ (fun φ => basicPointIdeal_le_ker D (φ.comp f) (h φ))

theorem complexPointBasicFactor_denominator (f : B →ₐ[ℂ] A)
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint (φ.comp f) ∈ D.toSet) : IsUnit (f D.f) := by
  apply (complex_points_isUnit _).mpr
  intro φ
  simpa [PrimeSpectrum.mem_zeroLocus, complexAlgebraPoint, RingHom.mem_ker] using (h φ).2

def complexPointBasicFactor (f : B →ₐ[ℂ] A)
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint (φ.comp f) ∈ D.toSet) :
    BasicConstructibleCoordinateRing D →ₐ[ℂ] A :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f)
    (f := Ideal.Quotient.liftₐ _ f (complexPointBasicFactor_kernel f D h))
    (complexPointBasicFactor_denominator f D h)

theorem complexPointBasicFactor_coordinateMap (f : B →ₐ[ℂ] A)
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint (φ.comp f) ∈ D.toSet) :
    (complexPointBasicFactor f D h).comp (basicConstructibleCoordinateMap D) = f := by
  ext b
  simp only [AlgHom.comp_apply, basicConstructibleCoordinateMap,
    IsScalarTower.toAlgHom_apply, complexPointBasicFactor,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem basicConstructibleFactor_ext {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (f g : BasicConstructibleCoordinateRing D →ₐ[ℂ] R)
    (he : f.comp (basicConstructibleCoordinateMap D) = g.comp (basicConstructibleCoordinateMap D)) :
    f = g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f))
  ext b
  exact AlgHom.congr_fun he b

theorem complexPointBasicFactor_Spec_square (f : B →ₐ[ℂ] A)
    (D : PrimeSpectrum.BasicConstructibleSetData B)
    (h : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint (φ.comp f) ∈ D.toSet) :
    Spec.map (CommRingCat.ofHom (complexPointBasicFactor f D h).toRingHom) ≫
      basicConstructibleInclusion D = Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [basicConstructibleInclusion, ← Spec.map_comp]
  apply congrArg Spec.map
  exact congrArg (fun g : B →ₐ[ℂ] A => CommRingCat.ofHom g.toRingHom)
    (complexPointBasicFactor_coordinateMap f D h)

end DiamondIntegral.Section5
