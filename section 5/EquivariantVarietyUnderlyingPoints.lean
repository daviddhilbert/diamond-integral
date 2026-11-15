import «section 5».ImmersedVarietyFieldPoints
import «section 5».ComplexAffineCoordinates

/-! Forgetting a finite action retains the actual scheme, coefficient
map and all extension-field points. This connects the geometric affine
partition with the original-complex VF chart coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

def EquivariantVariety.Object.underlyingVariety (X : EquivariantVariety.Object) : ComplexVariety where
  scheme := X.scheme
  toC := X.toC
  locally_finite_type := X.locally_finite_type
  compact := X.compact
  separated := X.separated
  reduced := X.reduced

def EquivariantVariety.Object.underlyingPointEquiv (X : EquivariantVariety.Object)
    {K : Type} [Field K] [Algebra ℂ K] :
    X.fieldPoint (K := K) ≃ X.underlyingVariety.Point (K := K) := Equiv.refl _

theorem EquivariantVariety.Object.underlyingVariety_isAffine (X : EquivariantVariety.Object)
    [IsAffine X.scheme] : IsAffine X.underlyingVariety.scheme := by
  exact (inferInstance : IsAffine X.scheme)

end DiamondIntegral.Section5
