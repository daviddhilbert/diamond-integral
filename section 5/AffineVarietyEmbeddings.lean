import «section 5».AffineCoordinateAlgebras
import «section 5».EquivariantAffineEmbedding
import «section 5».RationalAffineVarieties
import «section 5».VarietyMorphisms

/-! Every affine geometric finite-action variety has an actual
equivariant closed immersion into a rational diagonal affine space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] coordinateAlgebra coordinateAlgebra_finiteType

theorem Object.finite_level_overC (X : Object) :
    ∃ N : ℕ+, ∃ ρ : rootsOfUnity (N : ℕ) ℂ →* Aut X.scheme,
      X.action = ρ.comp (finiteRootProjection N) ∧ ∀ g, (ρ g).asIso.hom ≫ X.toC = X.toC := by
  obtain ⟨N, ρ, hρ⟩ := X.finite_level
  refine ⟨N, ρ, hρ, ?_⟩
  intro g
  obtain ⟨η, hη⟩ := finiteRootProjection_surjective N g
  have hh := X.overC η
  rw [hρ] at hh
  change (ρ (finiteRootProjection N η)).asIso.hom ≫ X.toC = X.toC at hh
  simpa only [hη] using hh

theorem affine_variety_diagonal_closed_embedding (X : Object) [IsAffine X.scheme] :
    ∃ n : ℕ, ∃ q : Fin n → ℚ, ∃ f : Morphism X (rationalAffineObject q), IsClosedImmersion f.hom := by
  obtain ⟨N, ρ, hρ, hρC⟩ := X.finite_level_overC
  let α := coordinateAlgebraAction X ρ hρC
  obtain ⟨n, x, w, hi, hEqui⟩ := finite_cyclic_equivariant_affine_embedding N α
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.scheme, ⊤) := MvPolynomial.aeval x
  let F := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let q := fun i => ((-w i : ℤ) : ℚ) / (N : ℕ)
  have hFC : F ≫ (rationalAffineObject q).toC =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) := by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))) = _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact φ.commutes c
  have hFE (g : rootsOfUnity (N : ℕ) ℂ) :
      (algebraSpecAction α g).asIso.hom ≫ F =
        F ≫ (algebraSpecAction (finiteDiagonalAlgebraAction N w) g).asIso.hom := by
    rw [algebraSpecAction_hom, algebraSpecAction_hom]
    dsimp only [F]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (hEqui g⁻¹)
  have hTarget : (rationalAffineObject q).action =
      (algebraSpecAction (finiteDiagonalAlgebraAction N w)).comp (finiteRootProjection N) := by
    simpa only [neg_neg] using rationalAffineObject_common_level N (fun i => -w i)
  let f : Morphism X (rationalAffineObject q) := {
    hom := X.scheme.isoSpec.hom ≫ F
    overC := by rw [Category.assoc, hFC]; exact coordinateIso_overC X
    equivariant := fun η => by
      rw [hρ, hTarget]
      change (ρ (finiteRootProjection N η)).asIso.hom ≫ (X.scheme.isoSpec.hom ≫ F) =
        (X.scheme.isoSpec.hom ≫ F) ≫
          (algebraSpecAction (finiteDiagonalAlgebraAction N w) (finiteRootProjection N η)).asIso.hom
      rw [← Category.assoc, coordinateIso_equivariant X ρ hρC, Category.assoc, hFE, ← Category.assoc] }
  letI : IsClosedImmersion F := hi
  exact ⟨n, q, f, inferInstanceAs (IsClosedImmersion (X.scheme.isoSpec.hom ≫ F))⟩

end DiamondIntegral.Section5.EquivariantVariety
