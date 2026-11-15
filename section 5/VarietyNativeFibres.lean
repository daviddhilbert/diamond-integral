import «section 5».VarietyNativeMorphisms
import «section 5».OriginalFibreIntegralVanishing

/-! The native fibres are exactly the full scheme-theoretic point
fibres, over every ambient-field point of the target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance fibreSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance fibreSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X Y : Object} (c : AffineVarietyPresentation X) (d : AffineVarietyPresentation Y)

def varietyNativeFibrePointMap (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ b : Y.fieldPoint (K := VFType (M := N)),
      {p : X.fieldPoint (K := VFType (M := N)) | f.fieldPointMap p = b} →
      nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c d f)
        (nativeMixedCode (varietyNativePointEquiv e G hB hc d b).val) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  intro b p
  let a := varietyNativePointEquiv e G hB hc c p.val
  refine ⟨a.val,(nativeMixedMapFibreAt_mem _ _ _).mpr ⟨a,rfl,?_⟩⟩
  change nativeMixedCode (varietyNativeMorphism e G hB hc c d f
    (varietyNativePointEquiv e G hB hc c p.val)).val = _
  rw [varietyNativeMorphism_point,p.property]

theorem varietyNativeFibrePointMap_bijective (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ b : Y.fieldPoint (K := VFType (M := N)),
      Function.Bijective (varietyNativeFibrePointMap e G hB hc c d f b) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  intro b
  let A := varietyNativePointEquiv e G hB hc c
  let B := varietyNativePointEquiv e G hB hc d
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply A.injective
    have he := congrArg Subtype.val hpq
    exact Subtype.ext he
  · intro x
    obtain ⟨a,ha,hb⟩ := (nativeMixedMapFibreAt_mem _ _ _).mp x.property
    let p := A.symm a
    have hp : f.fieldPointMap p = b := by
      apply B.injective
      rw [← varietyNativeMorphism_point]
      change varietyNativeMorphism e G hB hc c d f (A (A.symm a)) = B b
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext (nativeMixedCode_injective hb)
    refine ⟨⟨p,hp⟩,Subtype.ext ?_⟩
    change (A (A.symm a)).val = x.val
    rw [Equiv.apply_symm_apply]
    exact ha

def varietyNativeFibrePointEquiv (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ b : Y.fieldPoint (K := VFType (M := N)),
      {p : X.fieldPoint (K := VFType (M := N)) | f.fieldPointMap p = b} ≃
      nativeMixedMapFibreAt (varietyNativeMorphism e G hB hc c d f)
        (nativeMixedCode (varietyNativePointEquiv e G hB hc d b).val) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  intro b
  exact Equiv.ofBijective _ (varietyNativeFibrePointMap_bijective e G hB hc c d f b)

end DiamondIntegral.Section5.PuiseuxOriginal
