import «section 5».VarietyAffineNativeCharts
import «section 5».NativeVFFiniteAtlasMaps

/-! A finite affine immersed presentation realizes all extension-field
points as one native VF object over the original coefficient field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance atlasSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance atlasSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X : Object} (c : AffineVarietyPresentation X)

def varietyAtlasCount : ℕ := letI := c.presentation.finite; Fintype.card c.presentation.index

def varietyAtlasIndex : Fin (varietyAtlasCount c) ≃ c.presentation.index :=
  letI := c.presentation.finite; (Fintype.equivFin c.presentation.index).symm

def varietyNativeChart (i : Fin (varietyAtlasCount c)) : GammaGroundFiniteVFObject hc G.base :=
  letI := c.affine (varietyAtlasIndex c i)
  nativeGeometricAffineChart e G hB hc (c.presentation.piece (varietyAtlasIndex c i))

def varietyNativeObject : GammaGroundFiniteVFObject hc G.base :=
  nativeVFFiniteSum (varietyAtlasCount c) (varietyNativeChart e G hB hc c)

def varietyNativePointEquiv :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    X.fieldPoint (K := VFType (M := N)) ≃ (varietyNativeObject e G hB hc c).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  letI (i : c.presentation.index) := c.affine i
  exact c.presentation.fieldPointEquiv.symm |>.trans
    ((Equiv.sigmaCongrLeft (β := fun i => (c.presentation.piece i).fieldPoint
      (K := VFType (M := N))) (varietyAtlasIndex c)).symm |>.trans
      ((Equiv.sigmaCongrRight (fun i => nativeGeometricAffineChartEquiv e G hB hc
        (c.presentation.piece (varietyAtlasIndex c i)))).trans
          (nativeVFFiniteSumEquiv _ _)))

theorem varietyNativePointEquiv_chart (i : Fin (varietyAtlasCount c)) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    letI := c.affine (varietyAtlasIndex c i)
    ∀ p : (c.presentation.piece (varietyAtlasIndex c i)).fieldPoint (K := VFType (M := N)),
    (varietyNativePointEquiv e G hB hc c).symm
      (nativeVFFiniteSumInclusion _ (varietyNativeChart e G hB hc c) i
        (nativeGeometricAffineChartEquiv e G hB hc _ p)) =
      (c.presentation.inclusion (varietyAtlasIndex c i)).fieldPointMap p := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  letI := c.affine (varietyAtlasIndex c i)
  intro p
  rw [nativeVFFiniteSumInclusion_value]
  letI (j : c.presentation.index) := c.affine j
  let E := Equiv.sigmaCongrRight (fun j => nativeGeometricAffineChartEquiv e G hB hc
    (c.presentation.piece (varietyAtlasIndex c j)))
  change c.presentation.fieldPointEquiv
    ((Equiv.sigmaCongrLeft (varietyAtlasIndex c))
      (E.symm ((nativeVFFiniteSumEquiv _ (varietyNativeChart e G hB hc c)).symm
        ((nativeVFFiniteSumEquiv _ (varietyNativeChart e G hB hc c))
          ⟨i,nativeGeometricAffineChartEquiv e G hB hc _ p⟩)))) = _
  rw [Equiv.symm_apply_apply]
  change c.presentation.fieldPointEquiv
    ((Equiv.sigmaCongrLeft (varietyAtlasIndex c))
      ⟨i,(nativeGeometricAffineChartEquiv e G hB hc _).symm
        (nativeGeometricAffineChartEquiv e G hB hc _ p)⟩) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem varietyNativeObject_groundLabels : NativeGroundRVLabels (varietyNativeObject e G hB hc c).domain := by
  apply nativeVFFiniteSum_groundLabels
  intro i
  apply NativeGroundRVLabels.pureVF

end DiamondIntegral.Section5.PuiseuxOriginal
