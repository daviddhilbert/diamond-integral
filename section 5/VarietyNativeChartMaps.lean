import «section 5».VarietyNativeInclusions
import «section 5».VarietyAffineNativeMaps

/-! Regular maps subordinate to two actual affine atlases glue to a
native map whose point action is the original scheme morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance chartMapsSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance chartMapsSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X Y : Object} (c : AffineVarietyPresentation X) (d : AffineVarietyPresentation Y)

theorem varietyNativeChartMap_exists (f : Morphism X Y)
    (j : c.presentation.index → d.presentation.index)
    (g : ∀ i,Morphism (c.presentation.piece i) (d.presentation.piece (j i)))
    (h : ∀ i,(g i).hom ≫ (d.presentation.inclusion (j i)).hom =
      (c.presentation.inclusion i).hom ≫ f.hom) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∃ F : GammaGroundMap (varietyNativeObject e G hB hc c).domain
      (varietyNativeObject e G hB hc d).domain,
      ∀ p : X.fieldPoint (K := VFType (M := N)),
        F (varietyNativePointEquiv e G hB hc c p) =
          varietyNativePointEquiv e G hB hc d (f.fieldPointMap p) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  letI (i : c.presentation.index) := c.affine i
  letI (i : d.presentation.index) := d.affine i
  choose F hF using (fun i : c.presentation.index => nativeGeometricAffineMap_exists e G hB hc (g i))
  let maps (i : Fin (varietyAtlasCount c)) :=
    (varietyNativeInclusion e G hB hc d (j (varietyAtlasIndex c i))).comp (F (varietyAtlasIndex c i))
  obtain ⟨T,hT⟩ := nativeVFFiniteSum_map (varietyNativeChart e G hB hc c)
    (varietyNativeObject e G hB hc d).domain maps
  refine ⟨T,?_⟩
  intro p
  obtain ⟨⟨i,a⟩,ha⟩ := (nativeVFFiniteSumEquiv _ (varietyNativeChart e G hB hc c)).surjective
    (varietyNativePointEquiv e G hB hc c p)
  obtain ⟨q,rfl⟩ := (nativeGeometricAffineChartEquiv e G hB hc
    (c.presentation.piece (varietyAtlasIndex c i))).surjective a
  have hp : (c.presentation.inclusion (varietyAtlasIndex c i)).fieldPointMap q = p := by
    rw [← varietyNativePointEquiv_chart e G hB hc c i q]
    rw [nativeVFFiniteSumInclusion_value,ha,Equiv.symm_apply_apply]
  rw [← ha,← nativeVFFiniteSumInclusion_value,hT]
  change varietyNativeInclusion e G hB hc d (j (varietyAtlasIndex c i))
    (F (varietyAtlasIndex c i) (nativeGeometricAffineChartEquiv e G hB hc _ q)) = _
  rw [hF]
  apply (varietyNativePointEquiv e G hB hc d).symm.injective
  rw [varietyNativeInclusion_point,Equiv.symm_apply_apply]
  apply Subtype.ext
  change (q.val ≫ (g (varietyAtlasIndex c i)).hom) ≫
    (d.presentation.inclusion (j (varietyAtlasIndex c i))).hom = p.val ≫ f.hom
  rw [Category.assoc,h,← Category.assoc]
  exact congrArg (fun r : X.fieldPoint (K := VFType (M := N)) => r.val ≫ f.hom) hp

end DiamondIntegral.Section5.PuiseuxOriginal
