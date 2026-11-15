import «section 5».BasicConstructibleFactors
import Mathlib.Algebra.MvPolynomial.CommRing

/-! A rational tuple with an invertible common denominator gives an
actual algebra map. Its point formula and factorization into any basic
constructible target are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type} [CommRing A] [Algebra ℂ A]

theorem complex_algHom_unit_inverse (a : A) (ha : IsUnit a) (φ : A →ₐ[ℂ] ℂ) :
    φ (↑(ha.unit⁻¹) : A) = (φ a)⁻¹ := by
  have hp : a * (↑(ha.unit⁻¹) : A) = 1 := by
    change a * ha.unit.inv = 1
    exact (congrArg (fun z : A => z * ha.unit.inv) ha.unit_spec).symm.trans ha.unit.val_inv
  have h := congrArg φ hp
  rw [map_mul, map_one] at h
  have hn : φ a ≠ 0 := isUnit_iff_ne_zero.mp (ha.map φ.toRingHom)
  have he : φ (↑(ha.unit⁻¹) : A) = 1 / φ a := (eq_div_iff hn).mpr (by rw [mul_comm]; exact h)
  simpa only [one_div] using he

def unitRationalAlgebraMap {n m : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A :=
  MvPolynomial.aeval (fun j => f (p j) * (↑(hq.unit⁻¹) : A))

theorem unitRationalAlgebraMap_point {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) (φ : A →ₐ[ℂ] ℂ) :
    φ.comp (unitRationalAlgebraMap f p q hq) =
      MvPolynomial.aeval (fun j => φ (f (p j)) / φ (f q)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, unitRationalAlgebraMap, MvPolynomial.aeval_X,
    map_mul, complex_algHom_unit_inverse, div_eq_mul_inv]

variable [Algebra.FiniteType ℂ A] [IsReduced A]

def rationalBasicFactor {n m : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin m) ℂ))
    (hD : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint
      (MvPolynomial.aeval (fun j => φ (f (p j)) / φ (f q))) ∈ D.toSet) :
    BasicConstructibleCoordinateRing D →ₐ[ℂ] A :=
  complexPointBasicFactor (unitRationalAlgebraMap f p q hq) D
    (fun φ => (unitRationalAlgebraMap_point f p q hq φ) ▸ hD φ)

theorem rationalBasicFactor_coordinateMap {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) (D : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin m) ℂ))
    (hD : ∀ φ : A →ₐ[ℂ] ℂ, complexAlgebraPoint
      (MvPolynomial.aeval (fun j => φ (f (p j)) / φ (f q))) ∈ D.toSet) :
    (rationalBasicFactor f p q hq D hD).comp (basicConstructibleCoordinateMap D) =
      unitRationalAlgebraMap f p q hq :=
  complexPointBasicFactor_coordinateMap _ _ _

end DiamondIntegral.Section5
