import «section 5».VarietyAffineNativeCharts
import «section 5».AffineVFAlgebraMaps
import «section 5».ComplexAffineMorphisms

/-! Affine scheme morphisms have actual original-ground native maps,
with exactly their action on extension-field scheme points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance chartMapSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance chartMapSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
attribute [local instance] ComplexVariety.coordinateAlgebra Object.underlyingVariety_isAffine
variable {X Y : Object} [IsAffine X.scheme] [IsAffine Y.scheme]

theorem nativeGeometricAffineMap_exists (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∃ F : GammaGroundMap (nativeGeometricAffineChart e G hB hc X).domain
      (nativeGeometricAffineChart e G hB hc Y).domain,
      ∀ p : X.fieldPoint (K := VFType (M := N)),
        F (nativeGeometricAffineChartEquiv e G hB hc X p) =
          nativeGeometricAffineChartEquiv e G hB hc Y (f.fieldPointMap p) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  let P := Classical.choice X.underlyingVariety.affine_coordinate_presentation
  let Q := Classical.choice Y.underlyingVariety.affine_coordinate_presentation
  let g : X.underlyingVariety.Morphism Y.underlyingVariety := ⟨f.hom,f.overC⟩
  obtain ⟨F,hF⟩ := nativeAffineAlgebraMap_exists e G hB hc P Q g.affineAlgebraMap
  refine ⟨F,?_⟩
  intro p
  change F (nativeAffineAlgebraPointEquiv e G hB hc P
    (X.underlyingVariety.affinePointEquiv p)) =
    nativeAffineAlgebraPointEquiv e G hB hc Q (Y.underlyingVariety.affinePointEquiv (g.pointMap p))
  rw [g.affinePointEquiv_map]
  exact hF _

end DiamondIntegral.Section5.PuiseuxOriginal
