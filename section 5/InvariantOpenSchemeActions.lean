import «section 5».InvariantAffineCover
import Mathlib.AlgebraicGeometry.Restrict

/-! A scheme action restricts to every invariant open subscheme.
The restricted maps, their inverses and the equivariant inclusion are
actual scheme morphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {X : Scheme} {G : Type} [Group G]
variable (ρ : G →* Aut X) (U : X.Opens)
variable (hU : ∀ g x, schemePointAction ρ g x ∈ U ↔ x ∈ U)

def invariantOpenMap (g : G) : U.toScheme ⟶ U.toScheme :=
  (ρ g).asIso.hom.resLE U U (fun x hx => (hU g x).mpr hx)

@[reassoc]
theorem invariantOpenMap_ι (g : G) :
    invariantOpenMap ρ U hU g ≫ U.ι = U.ι ≫ (ρ g).asIso.hom :=
  Scheme.Hom.resLE_comp_ι _ _

theorem invariantOpenMap_one : invariantOpenMap ρ U hU 1 = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [invariantOpenMap_ι, map_one]
  rfl

theorem invariantOpenMap_mul (g h : G) :
    invariantOpenMap ρ U hU h ≫ invariantOpenMap ρ U hU g = invariantOpenMap ρ U hU (g * h) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, invariantOpenMap_ι, invariantOpenMap_ι_assoc]
  rw [map_mul]
  rfl

def invariantOpenSchemeAction : G →* Aut U.toScheme where
  toFun g := .of {
    hom := invariantOpenMap ρ U hU g
    inv := invariantOpenMap ρ U hU g⁻¹
    hom_inv_id := by rw [invariantOpenMap_mul, inv_mul_cancel, invariantOpenMap_one]
    inv_hom_id := by rw [invariantOpenMap_mul, mul_inv_cancel, invariantOpenMap_one] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact invariantOpenMap_one ρ U hU
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    exact (invariantOpenMap_mul ρ U hU g h).symm

theorem invariantOpenSchemeAction_equivariant (g : G) :
    (invariantOpenSchemeAction ρ U hU g).asIso.hom ≫ U.ι = U.ι ≫ (ρ g).asIso.hom :=
  invariantOpenMap_ι ρ U hU g

end DiamondIntegral.Section5
