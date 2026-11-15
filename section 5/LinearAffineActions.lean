import «section 5».PolynomialLinearMaps
import «section 5».RationalAffineVarieties
import «section 5».FiniteCyclicDiagonalization
import «section 5».SpecAlgebraActions

/-! Actual finite linear representations act on affine space by polynomial
coordinate changes. Character bases supply equivariant diagonal coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Module Classical AlgebraicGeometry CategoryTheory PuiseuxOriginal EquivariantVariety

variable {G : Type} [Group G]

def linearPolynomialAction {r : ℕ} (ρ : G →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) :
    G →* (MvPolynomial (Fin r) ℂ ≃ₐ[ℂ] MvPolynomial (Fin r) ℂ) where
  toFun g := linearPolynomialEquiv (ρ g⁻¹)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    change linearPolynomialMap (ρ (1⁻¹)).toLinearMap = AlgHom.id ℂ _
    simpa using linearPolynomialMap_id r
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    change linearPolynomialMap (ρ ((g * h)⁻¹)).toLinearMap =
      (linearPolynomialMap (ρ g⁻¹).toLinearMap).comp (linearPolynomialMap (ρ h⁻¹).toLinearMap)
    rw [← linearPolynomialMap_comp, mul_inv_rev, map_mul]
    rfl

def finiteLinearAffineObject {r : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) : Object :=
  affineObject (MvPolynomial (Fin r) ℂ) N (linearPolynomialAction ρ)

def diagonalLinearMap {n : ℕ} (a : Fin n → ℤ) (ζ : ℂˣ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x i := ((ζ ^ a i : ℂˣ) : ℂ) * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_comm, mul_left_comm, mul_assoc]

theorem linearPolynomialMap_diagonal {n : ℕ} (a : Fin n → ℤ) (ζ : ℂˣ) :
    linearPolynomialMap (diagonalLinearMap a ζ) = polynomialDiagonalAction a ζ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linearPolynomialMap, diagonalLinearMap, polynomialDiagonalAction, Pi.single_apply, apply_ite, ite_mul]

def linearRepresentation {r : ℕ}
    (ρ : G →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) : Representation ℂ G (Fin r → ℂ) where
  toFun g := (ρ g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

theorem character_basis_coordinates {r n : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))
    (b : Basis (Fin n) ℂ (Fin r → ℂ)) (a : Fin n → ℤ)
    (hb : ∀ ζ i, ρ ζ (b i) = ((ζ.val ^ a i : ℂˣ) : ℂ) • b i)
    (ζ : rootsOfUnity (N : ℕ) ℂ) :
    b.equivFun.toLinearMap.comp (ρ ζ).toLinearMap =
      (diagonalLinearMap a ζ.val).comp b.equivFun.toLinearMap := by
  apply b.ext
  intro i
  ext j
  by_cases hij : i = j
  · subst j; simp [LinearMap.comp_apply, hb, diagonalLinearMap]
  · simp [LinearMap.comp_apply, hb, diagonalLinearMap, Finsupp.single_apply, hij]

theorem character_basis_polynomial_coordinates {r n : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))
    (b : Basis (Fin n) ℂ (Fin r → ℂ)) (a : Fin n → ℤ)
    (hb : ∀ ζ i, ρ ζ (b i) = ((ζ.val ^ a i : ℂˣ) : ℂ) • b i)
    (ζ : rootsOfUnity (N : ℕ) ℂ) :
    (linearPolynomialMap (ρ ζ).toLinearMap).comp (linearPolynomialMap b.equivFun.toLinearMap) =
      (linearPolynomialMap b.equivFun.toLinearMap).comp (polynomialDiagonalAction a ζ.val) := by
  rw [← linearPolynomialMap_diagonal, ← linearPolynomialMap_comp, ← linearPolynomialMap_comp,
    character_basis_coordinates N ρ b a hb ζ]

theorem polynomialDiagonalAction_neg_inv {n : ℕ} (a : Fin n → ℤ) (ζ : ℂˣ) :
    polynomialDiagonalAction (fun i => -a i) ζ⁻¹ = polynomialDiagonalAction a ζ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialDiagonalAction, inv_zpow, zpow_neg]

def linearCoordinateSchemeIso {r n : ℕ} (e : (Fin r → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Spec (.of (MvPolynomial (Fin r) ℂ)) ≅ Spec (.of (MvPolynomial (Fin n) ℂ)) :=
  Scheme.Spec.mapIso (linearPolynomialEquiv e).toRingEquiv.toCommRingCatIso.op

theorem linearCoordinateSchemeIso_hom {r n : ℕ} (e : (Fin r → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    (linearCoordinateSchemeIso e).hom =
      Spec.map (CommRingCat.ofHom (linearPolynomialMap e.toLinearMap).toRingHom) := rfl

def characterBasisAffineIso {r n : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))
    (b : Basis (Fin n) ℂ (Fin r → ℂ)) (a : Fin n → ℤ)
    (hb : ∀ ζ i, ρ ζ (b i) = ((ζ.val ^ a i : ℂˣ) : ℂ) • b i) :
    EquivariantVariety.Iso (finiteLinearAffineObject N ρ)
      (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))) where
  iso := linearCoordinateSchemeIso b.equivFun
  overC := by
    rw [linearCoordinateSchemeIso_hom]
    change Spec.map (CommRingCat.ofHom (linearPolynomialMap b.equivFun.toLinearMap).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (linearPolynomialMap b.equivFun.toLinearMap).commutes c
  equivariant η := by
    rw [linearCoordinateSchemeIso_hom, rationalAffineObject_common_level]
    change (algebraSpecAction (linearPolynomialAction ρ) (finiteRootProjection N η)).asIso.hom ≫ _ =
      _ ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N (fun i => -a i))
        (finiteRootProjection N η)).asIso.hom
    rw [algebraSpecAction_hom, algebraSpecAction_hom, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change ((linearPolynomialMap (ρ ((finiteRootProjection N η)⁻¹)⁻¹).toLinearMap).comp
      (linearPolynomialMap b.equivFun.toLinearMap)).toRingHom =
      ((linearPolynomialMap b.equivFun.toLinearMap).comp
        (polynomialDiagonalAction (fun i => -a i) ((finiteRootProjection N η)⁻¹).val)).toRingHom
    rw [inv_inv]
    have hd : polynomialDiagonalAction (fun i => -a i) ((finiteRootProjection N η)⁻¹).val =
        polynomialDiagonalAction a (finiteRootProjection N η).val :=
      polynomialDiagonalAction_neg_inv a (finiteRootProjection N η).val
    rw [hd, character_basis_polynomial_coordinates N ρ b a hb]

theorem finite_linear_affine_diagonalization {r : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℂ (Fin r → ℂ), ∃ a : Fin n → ℤ,
      Nonempty (EquivariantVariety.Iso (finiteLinearAffineObject N ρ)
        (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ)))) ∧
      Nonempty (EquivariantVariety.Iso
        (finiteLinearAffineObject N (1 : rootsOfUnity (N : ℕ) ℂ →*
          ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))))
        (rationalAffineObject (fun _ : Fin n => (0 : ℚ)))) := by
  obtain ⟨n, b, a, hb⟩ := finite_cyclic_character_basis N (linearRepresentation ρ)
  refine ⟨n, b, a, ⟨characterBasisAffineIso N ρ b a hb⟩, ?_⟩
  have hi := characterBasisAffineIso N
    (1 : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) b
    (fun _ => (0 : ℤ)) (by intro ζ i; simp)
  simpa using Nonempty.intro hi

def diagonalLinearEquiv {n : ℕ} (a : Fin n → ℤ) (ζ : ℂˣ) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun := diagonalLinearMap a ζ
  invFun := diagonalLinearMap a ζ⁻¹
  left_inv x := by ext i; simp [diagonalLinearMap, ← mul_assoc, zpow_ne_zero _ (Units.ne_zero ζ)]
  right_inv x := by ext i; simp [diagonalLinearMap, ← mul_assoc, zpow_ne_zero _ (Units.ne_zero ζ)]
  map_add' := (diagonalLinearMap a ζ).map_add
  map_smul' := (diagonalLinearMap a ζ).map_smul

def diagonalLinearRepresentation {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) :
    rootsOfUnity (N : ℕ) ℂ →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) where
  toFun ζ := diagonalLinearEquiv a ζ.val
  map_one' := by ext x i; simp [diagonalLinearEquiv, diagonalLinearMap]
  map_mul' ζ ξ := by
    ext x i
    simp [diagonalLinearEquiv, diagonalLinearMap, mul_zpow, mul_assoc]

def diagonalFiniteAffineIso {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) :
    EquivariantVariety.Iso (finiteLinearAffineObject N (diagonalLinearRepresentation N a))
      (rationalAffineObject (fun i => (a i : ℚ) / (N : ℕ))) :=
  characterBasisAffineIso N (diagonalLinearRepresentation N a) (Pi.basisFun ℂ (Fin n)) a
    (by
      intro ζ i
      ext j
      by_cases hij : i = j
      · subst j; simp [diagonalLinearRepresentation, diagonalLinearEquiv, diagonalLinearMap]
      · simp [diagonalLinearRepresentation, diagonalLinearEquiv, diagonalLinearMap,
          Pi.basisFun_apply, Pi.single_apply, hij, Ne.symm hij])

def trivialFiniteAffineIso (r : ℕ) (N : ℕ+) :
    EquivariantVariety.Iso
      (finiteLinearAffineObject N (1 : rootsOfUnity (N : ℕ) ℂ →*
        ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))))
      (rationalAffineObject (fun _ : Fin r => (0 : ℚ))) := by
  have hi := characterBasisAffineIso N
    (1 : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))
    (Pi.basisFun ℂ (Fin r)) (fun _ => (0 : ℤ)) (by intro ζ i; simp)
  simpa using hi

end DiamondIntegral.Section5
