import «section 5».GeometricPreimageScissors
import «section 5».GeometricPreimageProducts

/-! The inverse value respects every defining geometric relation and
therefore gives an actual inverse-direction ring homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical PuiseuxOriginal

def EquivariantVariety.diagonalInvariant : EquivariantVariety.Invariant DiagonalConstructible.Ring where
  value := geometricPreimage
  unit := geometricPreimage_unit
  product := geometricPreimage_product
  iso := fun _ _ f => geometricPreimage_iso f
  empty := geometricPreimage_empty
  scissor := geometricPreimage_scissor

def EquivariantVariety.toDiagonalRing : EquivariantVariety.Ring →+* DiagonalConstructible.Ring :=
  EquivariantVariety.lift EquivariantVariety.diagonalInvariant

theorem EquivariantVariety.toDiagonalRing_objectClass (X : EquivariantVariety.Object) :
    EquivariantVariety.toDiagonalRing (EquivariantVariety.objectClass X) = geometricPreimage X :=
  EquivariantVariety.lift_objectClass EquivariantVariety.diagonalInvariant X

end DiamondIntegral.Section5
