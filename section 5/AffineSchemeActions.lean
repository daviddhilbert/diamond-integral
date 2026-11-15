import «section 5».InvariantAffineQuotients

/-! Coordinate-algebra actions induce actual scheme automorphisms with
the contravariance checked. Invariant reduced affine closed subschemes
inherit an action and their closed inclusions are equivariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {G : Type*} [Group G]

def algebraSpecAction (ρ : G →* (A ≃ₐ[ℂ] A)) : G →* Aut (Spec (.of A)) where
  toFun g := .of {
    hom := Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom)
    inv := Spec.map (CommRingCat.ofHom (ρ g).toRingHom)
    hom_inv_id := by
      rw [← Spec.map_comp]
      have he : CommRingCat.ofHom (ρ g).toRingHom ≫ CommRingCat.ofHom (ρ g⁻¹).toRingHom =
          𝟙 (CommRingCat.of A) := by
        ext a
        rw [map_inv]
        change (ρ g).symm (ρ g a) = a
        exact (ρ g).symm_apply_apply a
      rw [he, Spec.map_id]
    inv_hom_id := by
      rw [← Spec.map_comp]
      have he : CommRingCat.ofHom (ρ g⁻¹).toRingHom ≫ CommRingCat.ofHom (ρ g).toRingHom =
          𝟙 (CommRingCat.of A) := by
        ext a
        rw [map_inv]
        change ρ g ((ρ g).symm a) = a
        exact (ρ g).apply_symm_apply a
      rw [he, Spec.map_id] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (ρ (1⁻¹)).toRingHom) = 𝟙 _
    rw [inv_one, map_one]
    exact Spec.map_id _
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (ρ ((g * h)⁻¹)).toRingHom) =
      Spec.map (CommRingCat.ofHom (ρ h⁻¹).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom)
    rw [← Spec.map_comp]
    congr 1
    ext a
    change ρ ((g * h)⁻¹) a = ρ h⁻¹ (ρ g⁻¹ a)
    rw [mul_inv_rev, map_mul]
    rfl

theorem algebraSpecAction_hom (ρ : G →* (A ≃ₐ[ℂ] A)) (g : G) :
    (algebraSpecAction ρ g).asIso.hom =
      Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom) := rfl

theorem invariantClosedAffineInclusion_equivariant (ρ : G →* (A ≃ₐ[ℂ] A))
    (Z : Set (PrimeSpectrum A))
    (hZ : ∀ g x, PrimeSpectrum.comap (ρ g).toRingHom x ∈ Z ↔ x ∈ Z) (g : G) :
    closedAffineInclusion Z ≫ (algebraSpecAction ρ g).asIso.hom =
      (algebraSpecAction (invariantIdealQuotientAction ρ (PrimeSpectrum.vanishingIdeal Z)
        (invariantClosedIdeal_stable ρ Z hZ)) g).asIso.hom ≫ closedAffineInclusion Z := by
  rw [algebraSpecAction_hom, algebraSpecAction_hom, closedAffineInclusion,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1

end DiamondIntegral.Section5
