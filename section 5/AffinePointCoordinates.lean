import «section 5».ComplexPointsSeparate
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Actual extension-field points of a finite affine algebra presentation
are precisely tuples satisfying its kernel equations. Regular morphisms
between affine charts have actual polynomial coordinate functions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A K : Type} [CommRing A] [Algebra ℂ A] [Field K] [Algebra ℂ K]
variable {n : ℕ} (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hφ : Function.Surjective φ)

def affinePointCoordinates (ψ : A →ₐ[ℂ] K) : Fin n → K := fun i => ψ (φ (MvPolynomial.X i))

theorem affinePointCoordinates_aeval (ψ : A →ₐ[ℂ] K) :
    MvPolynomial.aeval (affinePointCoordinates φ ψ) = ψ.comp φ := by
  ext i
  exact MvPolynomial.aeval_X _ i

def affinePointCoordinateEquiv : (A →ₐ[ℂ] K) ≃
    {x : Fin n → K | RingHom.ker φ.toRingHom ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom} where
  toFun ψ := ⟨affinePointCoordinates φ ψ,by
    intro p hp
    rw [affinePointCoordinates_aeval]
    change ψ (φ p) = 0
    rw [show φ p = 0 from hp,map_zero]⟩
  invFun x := AlgHom.liftOfSurjective φ hφ (MvPolynomial.aeval x.val) x.property
  left_inv ψ := by
    apply AlgHom.ext
    intro a
    obtain ⟨p,rfl⟩ := hφ a
    rw [AlgHom.liftOfSurjective_apply]
    exact AlgHom.congr_fun (affinePointCoordinates_aeval φ ψ) p
  right_inv x := by
    apply Subtype.ext
    funext i
    change AlgHom.liftOfSurjective φ hφ (MvPolynomial.aeval x.val) x.property (φ (MvPolynomial.X i)) = x.val i
    rw [AlgHom.liftOfSurjective_apply,MvPolynomial.aeval_X]

variable {B : Type} [CommRing B] [Algebra ℂ B]
variable {m : ℕ} (θ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] B) (f : B →ₐ[ℂ] A)

include hφ in
theorem affineMorphism_polynomial_coordinates :
    ∃ P : Fin m → MvPolynomial (Fin n) ℂ, ∀ ψ : A →ₐ[ℂ] K,
      affinePointCoordinates θ (ψ.comp f) = fun j => MvPolynomial.aeval (affinePointCoordinates φ ψ) (P j) := by
  choose P hP using fun j => hφ (f (θ (MvPolynomial.X j)))
  refine ⟨P,?_⟩
  intro ψ
  funext j
  have he := AlgHom.congr_fun (affinePointCoordinates_aeval φ ψ) (P j)
  change ψ (f (θ (MvPolynomial.X j))) = _
  exact (congrArg ψ (hP j)).symm.trans he.symm

end DiamondIntegral.Section5
