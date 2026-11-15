import «section 5».RationalPolynomialActions
import «section 5».AffineVarietyObjects

/-! The affine space with its intrinsic rational diagonal action is an
actual geometric variety object. Contravariance is accounted for by the
negative algebra weights, so its complex-point action has the given weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory PuiseuxOriginal EquivariantVariety

theorem algebraSpecAction_comp {A : Type} [CommRing A] [Algebra ℂ A]
    {G H : Type} [Group G] [Group H] (ρ : G →* (A ≃ₐ[ℂ] A)) (π : H →* G) :
    algebraSpecAction (ρ.comp π) = (algebraSpecAction ρ).comp π := by
  apply MonoidHom.ext
  intro h
  apply Aut.ext
  apply CategoryTheory.Iso.ext
  simp only [algebraSpecAction_hom, MonoidHom.comp_apply, map_inv]

theorem compatibleRootCharacter_inv_system (η : CompatibleRoots ℂ) (q : ℚ) :
    compatibleRootCharacter η⁻¹ (Multiplicative.ofAdd q) =
      (compatibleRootCharacter η (Multiplicative.ofAdd q))⁻¹ := by
  change ((η.val ⟨q.den, q.den_pos⟩)⁻¹) ^ q.num = _
  exact inv_zpow _ _

theorem compatibleRootCharacter_neg (η : CompatibleRoots ℂ) (q : ℚ) :
    compatibleRootCharacter η (Multiplicative.ofAdd (-q)) =
      (compatibleRootCharacter η (Multiplicative.ofAdd q))⁻¹ :=
  map_inv (compatibleRootCharacter η) (Multiplicative.ofAdd q)

def rationalAffineObject {n : ℕ} (q : Fin n → ℚ) : EquivariantVariety.Object where
  scheme := Spec (.of (MvPolynomial (Fin n) ℂ))
  toC := Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ)))
  locally_finite_type := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  compact := inferInstance
  separated := inferInstance
  reduced := inferInstance
  action := algebraSpecAction (rationalPolynomialAction (fun i => -q i))
  overC := algebraSpecAction_overC _
  finite_level := by
    obtain ⟨N, a, ha⟩ := rational_tuple_common_level n (fun i => -q i)
    refine ⟨N, algebraSpecAction (finiteDiagonalAlgebraAction N a), ?_⟩
    rw [show (fun i => -q i) = (fun i => (a i : ℚ) / (N : ℕ)) from funext ha,
      rationalPolynomialAction_common_level, algebraSpecAction_comp]
  good _ := ⟨⊤, isAffineOpen_top _, fun _ => trivial⟩

theorem rationalAffineObject_common_level {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) :
    (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))).action =
      (algebraSpecAction (finiteDiagonalAlgebraAction N (fun i => -a i))).comp (finiteRootProjection N) := by
  change algebraSpecAction (rationalPolynomialAction (fun i => -((a i : ℚ) / (N : ℕ)))) = _
  have he : (fun i => -((a i : ℚ) / (N : ℕ))) =
      (fun i => ((-a i : ℤ) : ℚ) / (N : ℕ)) := by funext i; simp [neg_div]
  rw [he, rationalPolynomialAction_common_level, algebraSpecAction_comp]

theorem rationalAffineObject_complex_action {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    (fun i => (φ.comp (rationalPolynomialAction (fun j => -q j) η⁻¹).toAlgHom) (MvPolynomial.X i)) =
      rationalAction q η (fun i => φ (MvPolynomial.X i)) := by
  rw [rationalPolynomialAction_point]
  funext i
  simp only [rationalAction, compatibleRootCharacter_inv_system, compatibleRootCharacter_neg, inv_inv]

end DiamondIntegral.Section5
