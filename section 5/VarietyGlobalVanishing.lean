import «section 5».VarietyNativeChartIndependence
import «section 5».VarietyNativeFibres
import «section 5».GroundTaggedIntrinsicFibreValues

/-! The final Section 5 corollary for actual varieties and actual
regular morphisms. All affine encoding and parameter adapters are
constructed; only the recorded Section 3 integral inputs are used. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 EquivariantVariety
local instance globalVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance globalVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

def complexVarietyVolume (X : ComplexVariety) : ModifiedRing :=
  ambientBoundedVFVolume e hB hγ linear H (nativeVFClass
    (varietyNativeObject e G hB hc (Classical.choice X.finite_affine_presentation)))

theorem complexVarietyVolume_chart (X : ComplexVariety)
    (c : AffineVarietyPresentation X.trivialObject) :
    complexVarietyVolume e G hB hc hγ linear H X =
      ambientBoundedVFVolume e hB hγ linear H (nativeVFClass (varietyNativeObject e G hB hc c)) := by
  unfold complexVarietyVolume
  rw [varietyNativeClass_independent e G hB hc (Classical.choice X.finite_affine_presentation) c]

theorem corollary_global_vanishing {X Y : ComplexVariety} (f : X.Morphism Y)
    (c : AffineVarietyPresentation X.trivialObject) (d : AffineVarietyPresentation Y.trivialObject) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    let A := varietyNativeObject e G hB hc c
    let C := (varietyNativeObject e G hB hc d).domain
    let hC := varietyNativeObject_groundLabels e G hB hc d
    let F := varietyNativeMorphism e G hB hc c d f.trivialMorphism
    let hnt := ambientLaurentField_nontrivial e G hB
    ∀ (I : GroundTaggedFieldLiftInputs (hc := hc) hnt
        (varietyNativeObject e G hB hc d).vfArity (varietyNativeObject e G hB hc d).rvArity),
      (∀ b : Y.trivialObject.fieldPoint (K := VFType (M := N)),
        GroundTaggedIntrinsicFibreVanishes linear hnt hγ A C hC F I
          (varietyNativePointEquiv e G hB hc d b)) →
      complexVarietyVolume e G hB hc hγ linear H X = 0 := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  dsimp only
  intro I h
  rw [complexVarietyVolume_chart e G hB hc hγ linear H X c]
  exact ambientBoundedVFVolume_point_indexed_fibres e hB hγ linear H
    (varietyNativeObject e G hB hc c) (varietyNativeObject e G hB hc d).domain
    (varietyNativeObject_groundLabels e G hB hc d)
    (varietyNativeMorphism e G hB hc c d f.trivialMorphism) I
    (varietyNativePointEquiv e G hB hc d) h

end DiamondIntegral.Section5.PuiseuxOriginal
