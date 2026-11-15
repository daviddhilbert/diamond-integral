import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Scheme actions fixing a structural morphism are actual actions in
the category over that base. This keeps complex coefficients fixed in
the geometric variety comparison. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
universe u
variable {X B : Scheme.{u}} {G : Type*} [Group G]

def schemeActionOverBase (ρ : G →* Aut X) (c : X ⟶ B)
    (hc : ∀ g, (ρ g).asIso.hom ≫ c = c) : G →* Aut (Over.mk c) where
  toFun g := .of {
    hom := Over.homMk (ρ g).asIso.hom (hc g)
    inv := Over.homMk (ρ g).asIso.inv (by
      change (ρ g).asIso.inv ≫ c = c
      exact (congrArg (fun a : X ⟶ B => (ρ g).asIso.inv ≫ a) (hc g).symm).trans
        ((ρ g).asIso.inv_hom_id_assoc c))
    hom_inv_id := by
      apply Over.OverMorphism.ext
      exact (ρ g).asIso.hom_inv_id
    inv_hom_id := by
      apply Over.OverMorphism.ext
      exact (ρ g).asIso.inv_hom_id }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (ρ 1).asIso.hom = 𝟙 _
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (ρ (g * h)).asIso.hom = (ρ h).asIso.hom ≫ (ρ g).asIso.hom
    rw [map_mul]
    rfl

theorem schemeActionOverBase_hom (ρ : G →* Aut X) (c : X ⟶ B)
    (hc : ∀ g, (ρ g).asIso.hom ≫ c = c) (g : G) :
    (schemeActionOverBase ρ c hc g).asIso.hom.left = (ρ g).asIso.hom := rfl

end DiamondIntegral.Section5
