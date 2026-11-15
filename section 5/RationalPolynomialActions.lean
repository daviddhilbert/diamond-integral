import «section 5».DiagonalPolynomialActions
import «section 5».RationalDiagonalActions

/-! Intrinsic polynomial-algebra actions for rational character weights.
They agree with every common-denominator presentation, so no choice of a
finite root level enters the resulting action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory PuiseuxOriginal

theorem compatibleRootCharacter_mul_system (η θ : CompatibleRoots ℂ) (q : ℚ) :
    compatibleRootCharacter (η * θ) (Multiplicative.ofAdd q) =
      compatibleRootCharacter η (Multiplicative.ofAdd q) *
        compatibleRootCharacter θ (Multiplicative.ofAdd q) := by
  change ((η.val ⟨q.den, q.den_pos⟩) * (θ.val ⟨q.den, q.den_pos⟩)) ^ q.num = _
  exact mul_zpow _ _ _

theorem compatibleRootCharacter_one_system (q : ℚ) :
    compatibleRootCharacter (1 : CompatibleRoots ℂ) (Multiplicative.ofAdd q) = 1 := by
  change (1 : ℂˣ) ^ q.num = 1
  exact one_zpow _

def rationalPolynomialHom {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C
    ((compatibleRootCharacter η (Multiplicative.ofAdd (q i)) : ℂˣ) : ℂ) * MvPolynomial.X i)

theorem rationalPolynomialHom_one {n : ℕ} (q : Fin n → ℚ) :
    rationalPolynomialHom q 1 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialHom, compatibleRootCharacter_one_system]

theorem rationalPolynomialHom_mul {n : ℕ} (q : Fin n → ℚ) (η θ : CompatibleRoots ℂ) :
    rationalPolynomialHom q (η * θ) =
      (rationalPolynomialHom q η).comp (rationalPolynomialHom q θ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialHom, compatibleRootCharacter_mul_system, mul_comm, mul_left_comm, mul_assoc]

def rationalPolynomialEquiv {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom (rationalPolynomialHom q η) (rationalPolynomialHom q η⁻¹)
    (by rw [← rationalPolynomialHom_mul, mul_inv_cancel, rationalPolynomialHom_one])
    (by rw [← rationalPolynomialHom_mul, inv_mul_cancel, rationalPolynomialHom_one])

def rationalPolynomialAction {n : ℕ} (q : Fin n → ℚ) :
    CompatibleRoots ℂ →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) where
  toFun := rationalPolynomialEquiv q
  map_one' := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun (rationalPolynomialHom_one q) p
  map_mul' η θ := by
    apply AlgEquiv.ext
    intro p
    exact AlgHom.congr_fun (rationalPolynomialHom_mul q η θ) p

theorem rationalPolynomialHom_common_level {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (η : CompatibleRoots ℂ) :
    rationalPolynomialHom (fun i => (a i : ℚ) / (N : ℕ)) η =
      polynomialDiagonalAction a (η.val N) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialHom, polynomialDiagonalAction, compatibleRootCharacter_fraction]

theorem rationalPolynomialAction_common_level {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) :
    rationalPolynomialAction (fun i => (a i : ℚ) / (N : ℕ)) =
      (finiteDiagonalAlgebraAction N a).comp (finiteRootProjection N) := by
  apply MonoidHom.ext
  intro η
  apply AlgEquiv.ext
  intro p
  exact AlgHom.congr_fun (rationalPolynomialHom_common_level N a η) p

theorem rationalPolynomialAction_point {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    (fun i => (φ.comp (rationalPolynomialAction q η).toAlgHom) (MvPolynomial.X i)) =
      rationalAction q η (fun i => φ (MvPolynomial.X i)) := by
  funext i
  simp [rationalPolynomialAction, rationalPolynomialEquiv, rationalPolynomialHom, rationalAction]

end DiamondIntegral.Section5
