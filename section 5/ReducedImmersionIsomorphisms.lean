import «section 5».ReducedImmersionLifts
import Mathlib.CategoryTheory.Endomorphism

/-! Reduced immersed schemes with the same actual image are
canonically isomorphic over their ambient scheme. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
universe u
variable {X Y Z : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y]

def reducedImmersionIso (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) [IsImmersion g]
    (h : Set.range f = Set.range g) : X ≅ Y where
  hom := reducedImmersionLift g f h.le
  inv := reducedImmersionLift f g h.ge
  hom_inv_id := by
    apply (cancel_mono f).mp
    rw [Category.assoc, reducedImmersionLift_fac, reducedImmersionLift_fac, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    rw [Category.assoc, reducedImmersionLift_fac, reducedImmersionLift_fac, Category.id_comp]

theorem reducedImmersionIso_fac (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) [IsImmersion g]
    (h : Set.range f = Set.range g) : (reducedImmersionIso f g h).hom ≫ g = f :=
  reducedImmersionLift_fac g f h.le

theorem reducedImmersionIso_equivariant {G : Type*} [Group G]
    (f : X ⟶ Z) [IsImmersion f] (g : Y ⟶ Z) [IsImmersion g]
    (h : Set.range f = Set.range g)
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (ρZ : G →* Aut Z)
    (hf : ∀ q, (ρX q).asIso.hom ≫ f = f ≫ (ρZ q).asIso.hom)
    (hg : ∀ q, (ρY q).asIso.hom ≫ g = g ≫ (ρZ q).asIso.hom) (q : G) :
    (ρX q).asIso.hom ≫ (reducedImmersionIso f g h).hom =
      (reducedImmersionIso f g h).hom ≫ (ρY q).asIso.hom := by
  apply (cancel_mono g).mp
  calc
    ((ρX q).asIso.hom ≫ (reducedImmersionIso f g h).hom) ≫ g = (ρX q).asIso.hom ≫ f := by
      rw [Category.assoc, reducedImmersionIso_fac]
    _ = f ≫ (ρZ q).asIso.hom := hf q
    _ = ((reducedImmersionIso f g h).hom ≫ g) ≫ (ρZ q).asIso.hom := by rw [reducedImmersionIso_fac]
    _ = (reducedImmersionIso f g h).hom ≫ (g ≫ (ρZ q).asIso.hom) := Category.assoc _ _ _
    _ = (reducedImmersionIso f g h).hom ≫ ((ρY q).asIso.hom ≫ g) := by rw [hg q]
    _ = ((reducedImmersionIso f g h).hom ≫ (ρY q).asIso.hom) ≫ g := (Category.assoc _ _ _).symm

end DiamondIntegral.Section5
