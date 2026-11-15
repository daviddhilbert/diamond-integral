import «section 5».ReducedImmersionLifts
import «section 5».InvariantAffineCover

/-! Any scheme action preserving the image of a reduced immersion
restricts canonically to its source. Restriction commutes with inflation
of the acting group, so finite-level factorizations are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {X Z : Scheme} [AlgebraicGeometry.IsReduced X]
variable {G : Type} [Group G]
variable (f : X ⟶ Z) [IsImmersion f] (ρ : G →* Aut Z)
variable (hInv : ∀ g z, schemePointAction ρ g z ∈ Set.range f ↔ z ∈ Set.range f)

def reducedImmersionActionMap (g : G) : X ⟶ X :=
  reducedImmersionLift f (f ≫ (ρ g).asIso.hom) (by
    rintro _ ⟨x, rfl⟩
    exact (hInv g (f x)).mpr ⟨x, rfl⟩)

@[reassoc]
theorem reducedImmersionActionMap_fac (g : G) :
    reducedImmersionActionMap f ρ hInv g ≫ f = f ≫ (ρ g).asIso.hom :=
  reducedImmersionLift_fac _ _ _

theorem reducedImmersionActionMap_one : reducedImmersionActionMap f ρ hInv 1 = 𝟙 X := by
  apply (cancel_mono f).mp
  rw [reducedImmersionActionMap_fac, map_one]
  rfl

theorem reducedImmersionActionMap_mul (g h : G) :
    reducedImmersionActionMap f ρ hInv h ≫ reducedImmersionActionMap f ρ hInv g =
      reducedImmersionActionMap f ρ hInv (g * h) := by
  apply (cancel_mono f).mp
  simp only [Category.assoc, reducedImmersionActionMap_fac, reducedImmersionActionMap_fac_assoc]
  rw [map_mul]
  rfl

def reducedImmersionSchemeAction : G →* Aut X where
  toFun g := .of {
    hom := reducedImmersionActionMap f ρ hInv g
    inv := reducedImmersionActionMap f ρ hInv g⁻¹
    hom_inv_id := by rw [reducedImmersionActionMap_mul, inv_mul_cancel, reducedImmersionActionMap_one]
    inv_hom_id := by rw [reducedImmersionActionMap_mul, mul_inv_cancel, reducedImmersionActionMap_one] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact reducedImmersionActionMap_one f ρ hInv
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    exact (reducedImmersionActionMap_mul f ρ hInv g h).symm

theorem reducedImmersionSchemeAction_fac (g : G) :
    (reducedImmersionSchemeAction f ρ hInv g).asIso.hom ≫ f = f ≫ (ρ g).asIso.hom :=
  reducedImmersionActionMap_fac f ρ hInv g

theorem reducedImmersionSchemeAction_comp {H : Type} [Group H] (π : H →* G)
    (hH : ∀ h z, schemePointAction (ρ.comp π) h z ∈ Set.range f ↔ z ∈ Set.range f) :
    reducedImmersionSchemeAction f (ρ.comp π) hH = (reducedImmersionSchemeAction f ρ hInv).comp π := by
  apply MonoidHom.ext
  intro h
  apply Aut.ext
  apply Iso.ext
  apply (cancel_mono f).mp
  change (reducedImmersionSchemeAction f (ρ.comp π) hH h).asIso.hom ≫ f =
    (reducedImmersionSchemeAction f ρ hInv (π h)).asIso.hom ≫ f
  rw [reducedImmersionSchemeAction_fac, reducedImmersionSchemeAction_fac]
  rfl

end DiamondIntegral.Section5
