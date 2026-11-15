import «section 5».ImmersionCoordinateGraphs
import «section 5».TupleGraphIsomorphisms

/-! Two equivariant immersions of the same geometric variety give
isomorphic actual diagonal constructible image objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ) {Y : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Y (rationalAffineObject r))
variable [IsImmersion f.hom] [IsImmersion g.hom]

def diagonalIsoOfImmersions : DiagonalConstructible.Iso
    (DiagonalConstructible.immersedObject q f) (DiagonalConstructible.immersedObject r g) :=
  diagonalIsoOfTupleGraph _ _ (immersionCoordinateGraph q r f g).domain
    (immersionCoordinateGraph q r f g).definable (immersionCoordinateGraph q r f g).invariant
    (immersionCoordinateGraph_contained q r f g)
    (by
      intro x
      obtain ⟨y, hy, hxy⟩ := immersionCoordinateGraph_left_exists q r f g x.val x.property
      exact ⟨⟨y, hy⟩, hxy, fun z hz => Subtype.ext
        (immersionCoordinateGraph_left_unique q r f g x.val z.val y hz hxy)⟩)
    (by
      intro y
      obtain ⟨x, hx, hxy⟩ := immersionCoordinateGraph_right_exists q r f g y.val y.property
      exact ⟨⟨x, hx⟩, hxy, fun z hz => Subtype.ext
        (immersionCoordinateGraph_right_unique q r f g y.val z.val x hz hxy)⟩)

theorem immersedObject_class_eq :
    DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject q f) =
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject r g) :=
  DiagonalConstructible.objectClass_iso (diagonalIsoOfImmersions q r f g)

end DiamondIntegral.Section5
