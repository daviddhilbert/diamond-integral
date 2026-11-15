import «section 5».EquivariantVarietyUnderlyingPoints
import «section 5».AffineVFPointEquiv

/-! Every affine geometric chart is realized by an actual native VF
object, and its ambient-field scheme points are exactly that object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open DiamondIntegral.Section3
local instance varietyChartSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance varietyChartSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))

attribute [local instance] ComplexVariety.coordinateAlgebra

def nativeGeometricAffineChart (X : EquivariantVariety.Object) [IsAffine X.scheme] :
    GammaGroundFiniteVFObject hc G.base := by
  letI := X.underlyingVariety_isAffine
  let P := Classical.choice X.underlyingVariety.affine_coordinate_presentation
  exact nativeAffineVFObject e G hB hc P.equations

def nativeGeometricAffineChartEquiv (X : EquivariantVariety.Object) [IsAffine X.scheme] :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    X.fieldPoint (K := VFType (M := N)) ≃ (nativeGeometricAffineChart e G hB hc X).domain := by
  letI := X.underlyingVariety_isAffine
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  let P := Classical.choice X.underlyingVariety.affine_coordinate_presentation
  exact X.underlyingPointEquiv.trans (nativeAffineVarietyPointEquiv e G hB hc X.underlyingVariety P)

end DiamondIntegral.Section5.PuiseuxOriginal
