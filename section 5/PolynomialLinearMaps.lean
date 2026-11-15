import «section 5».ComplexPointsSeparate
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical

def linearPolynomialMap {n m : ℕ} (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (f (Pi.single j 1) i) * MvPolynomial.X j)

theorem linearPolynomialMap_coordinate {n m : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (x : Fin m → ℂ) (i : Fin n) :
    (MvPolynomial.aeval x).comp (linearPolynomialMap f) (MvPolynomial.X i) = f x i := by
  have hx : ∑ j, x j • Pi.single j (1 : ℂ) = x := by
    ext k
    simp [Pi.single_apply]
  have he := congrArg (fun y : Fin n → ℂ => y i) (congrArg f hx)
  simpa [linearPolynomialMap, map_sum, map_smul, Finset.sum_apply, smul_eq_mul,
    mul_comm] using he

theorem linearPolynomialMap_point {n m : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (x : Fin m → ℂ) :
    (MvPolynomial.aeval x).comp (linearPolynomialMap f) = MvPolynomial.aeval (f x) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa using linearPolynomialMap_coordinate f x i

theorem linearPolynomialMap_comp {n m k : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (g : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    linearPolynomialMap (f.comp g) = (linearPolynomialMap g).comp (linearPolynomialMap f) := by
  apply complex_points_algHom_ext
  intro φ
  have hφ : φ = MvPolynomial.aeval (fun j => φ (MvPolynomial.X j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  rw [hφ, ← AlgHom.comp_assoc, linearPolynomialMap_point, linearPolynomialMap_point,
    linearPolynomialMap_point]
  rfl

theorem linearPolynomialMap_id (n : ℕ) :
    linearPolynomialMap (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linearPolynomialMap, Pi.single_apply]

def linearPolynomialEquiv {n m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  AlgEquiv.ofAlgHom (linearPolynomialMap e.toLinearMap) (linearPolynomialMap e.symm.toLinearMap)
    (by rw [← linearPolynomialMap_comp]; simpa using linearPolynomialMap_id m)
    (by rw [← linearPolynomialMap_comp]; simpa using linearPolynomialMap_id n)

end DiamondIntegral.Section5
