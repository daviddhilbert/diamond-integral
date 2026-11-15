import «section 5».Section5DischargedInputs
import «section 5».VarietyGlobalVanishing

/-! The actual-variety corollary with the ground and every intrinsic
F(b) lifting/kernel input constructed, and Gamma-linearity proved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 EquivariantVariety
local instance dischargedVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance dischargedVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real=Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable (hγ : ∀ γ∈G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)

def complexVarietyVolume_discharged (X : ComplexVariety) : ModifiedRing :=
  complexVarietyVolume e G hB hc hγ GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc) X

theorem corollary_global_vanishing_discharged {X Y : ComplexVariety} (f : X.Morphism Y)
    (c : AffineVarietyPresentation X.trivialObject) (d : AffineVarietyPresentation Y.trivialObject) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    let A := varietyNativeObject e G hB hc c
    let C := (varietyNativeObject e G hB hc d).domain
    let hC := varietyNativeObject_groundLabels e G hB hc d
    let F := varietyNativeMorphism e G hB hc c d f.trivialMorphism
    let hnt := ambientLaurentField_nontrivial e G hB
    (∀ b : Y.trivialObject.fieldPoint (K := VFType (M := N)),
      GroundTaggedIntrinsicFibreVanishes GammaQE.gamma_piecewise_rational_affine hnt hγ A C hC F
        (completedGroundTaggedFieldLiftInputs G hc hnt
          (varietyNativeObject e G hB hc d).vfArity (varietyNativeObject e G hB hc d).rvArity)
        (varietyNativePointEquiv e G hB hc d b)) →
      complexVarietyVolume_discharged e G hB hc hγ X=0 := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  dsimp only
  intro h
  exact corollary_global_vanishing e G hB hc hγ GammaQE.gamma_piecewise_rational_affine
    (completed18GroundLiftInput G hc) f c d
    (completedGroundTaggedFieldLiftInputs G hc (ambientLaurentField_nontrivial e G hB)
      (varietyNativeObject e G hB hc d).vfArity (varietyNativeObject e G hB hc d).rvArity) h

end DiamondIntegral.Section5.PuiseuxOriginal
