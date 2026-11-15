import «section 5».VarietyNativeAtlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance atlasInclSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance atlasInclSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X : Object} (c : AffineVarietyPresentation X)

theorem varietyNativeInclusion_exists (j : c.presentation.index) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    letI := c.affine j
    ∃ F : GammaGroundMap (nativeGeometricAffineChart e G hB hc (c.presentation.piece j)).domain
      (varietyNativeObject e G hB hc c).domain,
    ∀ p : (c.presentation.piece j).fieldPoint (K := VFType (M := N)),
      (varietyNativePointEquiv e G hB hc c).symm
        (F (nativeGeometricAffineChartEquiv e G hB hc _ p)) =
        (c.presentation.inclusion j).fieldPointMap p := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  letI (i : c.presentation.index) := c.affine i
  obtain ⟨i,rfl⟩ := (varietyAtlasIndex c).surjective j
  exact ⟨nativeVFFiniteSumInclusion _ (varietyNativeChart e G hB hc c) i,
    varietyNativePointEquiv_chart e G hB hc c i⟩

def varietyNativeInclusion (j : c.presentation.index) :
    letI := c.affine j
    GammaGroundMap (nativeGeometricAffineChart e G hB hc (c.presentation.piece j)).domain
      (varietyNativeObject e G hB hc c).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact Classical.choose (varietyNativeInclusion_exists e G hB hc c j)

theorem varietyNativeInclusion_point (j : c.presentation.index) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    letI := c.affine j
    ∀ p : (c.presentation.piece j).fieldPoint (K := VFType (M := N)),
    (varietyNativePointEquiv e G hB hc c).symm
      (varietyNativeInclusion e G hB hc c j (nativeGeometricAffineChartEquiv e G hB hc _ p)) =
      (c.presentation.inclusion j).fieldPointMap p := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact Classical.choose_spec (varietyNativeInclusion_exists e G hB hc c j)

end DiamondIntegral.Section5.PuiseuxOriginal
