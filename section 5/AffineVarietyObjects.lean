import «section 5».EquivariantVarietyRing
import «section 5».AffineSchemeActions

/-! Actual reduced finite-type complex affine schemes with finite root
actions are objects of the geometric equivariant variety presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory

theorem algebraSpecAction_overC {A : Type} [CommRing A] [Algebra ℂ A]
    {H : Type} [Group H] (ρ : H →* (A ≃ₐ[ℂ] A)) (h : H) :
    (algebraSpecAction ρ h).asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) := by
  rw [algebraSpecAction_hom, ← Spec.map_comp]
  congr 1
  ext c
  exact (ρ h⁻¹).commutes c

def affineObject (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    [IsReduced A] (N : ℕ+) (ρ : rootsOfUnity (N : ℕ) ℂ →* (A ≃ₐ[ℂ] A)) : Object where
  scheme := Spec (.of A)
  toC := Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
  locally_finite_type := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ A)
  compact := inferInstance
  separated := inferInstance
  reduced := inferInstance
  action := (algebraSpecAction ρ).comp (finiteRootProjection N)
  overC h := algebraSpecAction_overC ρ (finiteRootProjection N h)
  finite_level := ⟨N, algebraSpecAction ρ, rfl⟩
  good x := ⟨⊤, isAffineOpen_top _, fun _ => trivial⟩

end DiamondIntegral.Section5.EquivariantVariety
