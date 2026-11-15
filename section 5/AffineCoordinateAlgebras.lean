import «section 5».SpecAlgebraActions
import «section 5».VarietyImmersedObjects
import Mathlib.CategoryTheory.Conj

/-! The actual coordinate algebra of an affine geometric variety over
the complex base. Finite type and equivariant transport are derived from
the structural scheme morphism and its actual action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] Object.locally_finite_type Object.reduced

def coordinateAlgebra (X : Object) [IsAffine X.scheme] : Algebra ℂ Γ(X.scheme, ⊤) :=
  (Spec.preimage (X.scheme.isoSpec.inv ≫ X.toC)).hom.toAlgebra

attribute [local instance] coordinateAlgebra

theorem coordinateSpec_toC (X : Object) [IsAffine X.scheme] :
    Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) = X.scheme.isoSpec.inv ≫ X.toC := by
  change Spec.map (Spec.preimage (X.scheme.isoSpec.inv ≫ X.toC)) = _
  exact Spec.map_preimage _

theorem coordinateIso_overC (X : Object) [IsAffine X.scheme] :
    X.scheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) = X.toC := by
  rw [coordinateSpec_toC, ← Category.assoc, X.scheme.isoSpec.hom_inv_id, Category.id_comp]

theorem coordinateAlgebra_finiteType (X : Object) [IsAffine X.scheme] :
    Algebra.FiniteType ℂ Γ(X.scheme, ⊤) := by
  have hFT : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤)))) := by
    rw [coordinateSpec_toC]
    infer_instance
  have hraw : (algebraMap ℂ Γ(X.scheme, ⊤)).FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hFT
  exact RingHom.finiteType_algebraMap.mp hraw

def coordinateSchemeAction (X : Object) [IsAffine X.scheme] {G : Type} [Group G]
    (σ : G →* Aut X.scheme) : G →* Aut (Spec (.of Γ(X.scheme, ⊤))) :=
  X.scheme.isoSpec.conjAut.toMonoidHom.comp σ

theorem coordinateSchemeAction_hom (X : Object) [IsAffine X.scheme] {G : Type} [Group G]
    (σ : G →* Aut X.scheme) (g : G) :
    (coordinateSchemeAction X σ g).asIso.hom = X.scheme.isoSpec.inv ≫ (σ g).asIso.hom ≫ X.scheme.isoSpec.hom := by
  change (X.scheme.isoSpec.conjAut (σ g)).asIso.hom = _
  rw [CategoryTheory.Iso.conjAut_apply]
  rfl

theorem coordinateSchemeAction_overC (X : Object) [IsAffine X.scheme] {G : Type} [Group G]
    (σ : G →* Aut X.scheme) (hσ : ∀ g, (σ g).asIso.hom ≫ X.toC = X.toC) (g : G) :
    (coordinateSchemeAction X σ g).asIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) := by
  rw [coordinateSchemeAction_hom, coordinateSpec_toC]
  simp only [Category.assoc, X.scheme.isoSpec.hom_inv_id_assoc, hσ]

def coordinateAlgebraAction (X : Object) [IsAffine X.scheme] {G : Type} [Group G]
    (σ : G →* Aut X.scheme) (hσ : ∀ g, (σ g).asIso.hom ≫ X.toC = X.toC) :
    G →* (Γ(X.scheme, ⊤) ≃ₐ[ℂ] Γ(X.scheme, ⊤)) :=
  specActionAlgebraAction (coordinateSchemeAction X σ) (coordinateSchemeAction_overC X σ hσ)

theorem coordinateIso_equivariant (X : Object) [IsAffine X.scheme] {G : Type} [Group G]
    (σ : G →* Aut X.scheme) (hσ : ∀ g, (σ g).asIso.hom ≫ X.toC = X.toC) (g : G) :
    (σ g).asIso.hom ≫ X.scheme.isoSpec.hom =
      X.scheme.isoSpec.hom ≫ (algebraSpecAction (coordinateAlgebraAction X σ hσ) g).asIso.hom := by
  unfold coordinateAlgebraAction
  rw [algebraSpecAction_specActionAlgebraAction, coordinateSchemeAction_hom]
  simp only [← Category.assoc, X.scheme.isoSpec.hom_inv_id, Category.id_comp]

end DiamondIntegral.Section5.EquivariantVariety
