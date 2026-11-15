import «section 5».LinearAffineActions
import «section 5».RawGeometricComparison
import «section 5».RESLinearActionQuotient

/-! The geometric ideal uses every actual finite linear representation.
Its ideal closure includes multiplication by every equivariant variety.
Diagonalization identifies it exactly with the native comparison ideal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory PuiseuxOriginal Topology

 def EquivariantVariety.linearActionRelations : Set EquivariantVariety.Ring :=
  {z | ∃ r : ℕ, ∃ N : ℕ+,
    ∃ ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)),
    z = EquivariantVariety.objectClass (finiteLinearAffineObject N ρ) -
      EquivariantVariety.objectClass (finiteLinearAffineObject N
        (1 : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))))}

def EquivariantVariety.linearActionIdeal : Ideal EquivariantVariety.Ring :=
  Ideal.span EquivariantVariety.linearActionRelations

theorem finite_linear_difference_mem {r : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))) :
    EquivariantVariety.objectClass (finiteLinearAffineObject N ρ) -
      EquivariantVariety.objectClass (finiteLinearAffineObject N
        (1 : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))) ∈
      EquivariantVariety.linearActionIdeal := Ideal.subset_span ⟨r, N, ρ, rfl⟩

theorem finite_linear_product_difference_mem {r : ℕ} (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ)))
    (X : EquivariantVariety.Object) :
    EquivariantVariety.objectClass X *
      (EquivariantVariety.objectClass (finiteLinearAffineObject N ρ) -
        EquivariantVariety.objectClass (finiteLinearAffineObject N
          (1 : rootsOfUnity (N : ℕ) ℂ →* ((Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))))) ∈
      EquivariantVariety.linearActionIdeal :=
  Ideal.mul_mem_left _ _ (finite_linear_difference_mem N ρ)

theorem rational_diagonal_difference_mem {n : ℕ} (q : Fin n → ℚ) :
    EquivariantVariety.objectClass (rationalAffineObject q) -
      EquivariantVariety.objectClass (rationalAffineObject (fun _ : Fin n => (0 : ℚ))) ∈
      EquivariantVariety.linearActionIdeal := by
  obtain ⟨N, a, ha⟩ := rational_tuple_common_level n q
  have he : q = fun i => (a i : ℚ) / (N : ℕ) := funext ha
  rw [he]
  have h := finite_linear_difference_mem N (diagonalLinearRepresentation N a)
  rw [EquivariantVariety.objectClass_iso (diagonalFiniteAffineIso N a),
    EquivariantVariety.objectClass_iso (trivialFiniteAffineIso n N)] at h
  exact h

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_affineSpace {n : ℕ} (q : Fin n → ℚ) :
    geometricValue (affineSpace q) = EquivariantVariety.objectClass (rationalAffineObject q) := by
  exact (constructibleClass_set_congr (rationalAffineObject q) _ Set.univ
    (complexSpectrumExtension_constructible _ _) IsConstructible.univ
    (complexSpectrumExtension_invariant _ _ _ (affineSpace q).invariant)
    (EquivariantVariety.Object.Invariant.univ _)
    (complexSpectrumExtension_univ (affineSpace q).definable)).trans
      (constructibleClass_univ _)

theorem PuiseuxOriginal.DiagonalConstructible.toVarietyRing_affineSpace {n : ℕ} (q : Fin n → ℚ) :
    toVarietyRing (objectClass (affineSpace q)) =
      EquivariantVariety.objectClass (rationalAffineObject q) := by
  rw [toVarietyRing_objectClass, geometricValue_affineSpace]

theorem PuiseuxOriginal.DiagonalConstructible.affine_difference_mem {n : ℕ} (q : Fin n → ℚ) :
    objectClass (affineSpace q) - objectClass (affineSpace (fun _ : Fin n => (0 : ℚ))) ∈
      linearActionIdeal := by
  have h : objectClass (product unit (affineSpace q)) -
      objectClass (product unit (affineSpace (fun _ : Fin n => (0 : ℚ)))) ∈ linearActionIdeal :=
    Ideal.subset_span ⟨unit, n, q, rfl⟩
  simpa only [objectClass_product, objectClass_unit, one_mul] using h

theorem geometric_linearActionIdeal_correspondence :
    Ideal.map DiagonalConstructible.toVarietyRing DiagonalConstructible.linearActionIdeal =
      EquivariantVariety.linearActionIdeal := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro z ⟨X, n, q, rfl⟩
    change DiagonalConstructible.toVarietyRing _ ∈ EquivariantVariety.linearActionIdeal
    rw [map_sub, DiagonalConstructible.objectClass_product,
      DiagonalConstructible.objectClass_product, map_mul, map_mul,
      DiagonalConstructible.toVarietyRing_affineSpace,
      DiagonalConstructible.toVarietyRing_affineSpace, ← mul_sub]
    exact Ideal.mul_mem_left _ _ (rational_diagonal_difference_mem q)
  · apply Ideal.span_le.mpr
    rintro z ⟨r, N, ρ, rfl⟩
    obtain ⟨n, b, a, ⟨e⟩, ⟨e0⟩⟩ := finite_linear_affine_diagonalization N ρ
    rw [EquivariantVariety.objectClass_iso e, EquivariantVariety.objectClass_iso e0]
    have hm := Ideal.mem_map_of_mem DiagonalConstructible.toVarietyRing
      (DiagonalConstructible.affine_difference_mem (fun i => (a i : ℚ) / (N : ℕ)))
    rw [map_sub, DiagonalConstructible.toVarietyRing_affineSpace,
      DiagonalConstructible.toVarietyRing_affineSpace] at hm
    exact hm

end DiamondIntegral.Section5
