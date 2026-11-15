import «section 5».VarietyNativeChartIndependence
import «section 5».NativeSourceFibreTransfer
import «section 5».NativeTargetFibreTransfer

/-! Actual scheme morphism encodings commute with chart changes.
The induced source and target fibre transports retain exact bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance fibreChangesSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance fibreChangesSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X Y : Object}

theorem varietyNativeChartChange_point (c c' : AffineVarietyPresentation X) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ p : X.fieldPoint (K := VFType (M := N)),
      (varietyNativeChartChange e G hB hc c c').map (varietyNativePointEquiv e G hB hc c p) =
        varietyNativePointEquiv e G hB hc c' p := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  intro p
  change varietyNativeMorphism e G hB hc c c' (Morphism.id X) _ = _
  rw [varietyNativeMorphism_point]
  apply congrArg (varietyNativePointEquiv e G hB hc c')
  apply Subtype.ext
  exact Category.comp_id _

theorem varietyNativeMorphism_source_change (c c' : AffineVarietyPresentation X)
    (d : AffineVarietyPresentation Y) (f : Morphism X Y)
    (a : (varietyNativeObject e G hB hc c).domain) :
    varietyNativeMorphism e G hB hc c' d f ((varietyNativeChartChange e G hB hc c c').map a) =
      varietyNativeMorphism e G hB hc c d f a := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  obtain ⟨p,rfl⟩ := (varietyNativePointEquiv e G hB hc c).surjective a
  rw [varietyNativeChartChange_point,varietyNativeMorphism_point,varietyNativeMorphism_point]

theorem varietyNativeMorphism_target_change (c : AffineVarietyPresentation X)
    (d d' : AffineVarietyPresentation Y) (f : Morphism X Y)
    (a : (varietyNativeObject e G hB hc c).domain) :
    varietyNativeMorphism e G hB hc c d' f a =
      (varietyNativeChartChange e G hB hc d d').map (varietyNativeMorphism e G hB hc c d f a) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  obtain ⟨p,rfl⟩ := (varietyNativePointEquiv e G hB hc c).surjective a
  rw [varietyNativeMorphism_point,varietyNativeMorphism_point,varietyNativeChartChange_point]

def varietyNativeSourceFibreBijection (c c' : AffineVarietyPresentation X)
    (d : AffineVarietyPresentation Y) (f : Morphism X Y)
    (z : Fin ((varietyNativeObject e G hB hc d).vfArity + (varietyNativeObject e G hB hc d).rvArity) → N) :
    GammaGroundBijection (nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c d f) z)
      (nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c' d f) z) :=
  nativeSourceFibreBijection _ _ (varietyNativeChartChange e G hB hc c c')
    (varietyNativeMorphism_source_change e G hB hc c c' d f) z

def varietyNativeTargetFibreBijection (c : AffineVarietyPresentation X)
    (d d' : AffineVarietyPresentation Y) (f : Morphism X Y)
    (b : (varietyNativeObject e G hB hc d).domain) :
    GammaGroundBijection
      (nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c d f) (nativeMixedCode b.val))
      (sortedTransferMixedDomain
        (nativeMixedMap_parameter_transfer (varietyNativeChartChange e G hB hc d d').map b)
        (nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c d' f)
          (nativeMixedCode ((varietyNativeChartChange e G hB hc d d').map b).val))) :=
  nativeTargetChangedFibreBijection (varietyNativeObject e G hB hc c) _ _
    (varietyNativeChartChange e G hB hc d d')
    (varietyNativeMorphism_target_change e G hB hc c d d' f) b

end DiamondIntegral.Section5.PuiseuxOriginal
