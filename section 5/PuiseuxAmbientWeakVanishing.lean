import «section 5».PuiseuxAmbientVFFubiniVanishing
import «section 5».NativeWeakVFFubiniVanishing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance ambientWeakVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientWeakVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := N)} {G : GammaGroundContext N}

theorem ambientBoundedVFVolume_weak_fibre_vanishing
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := N) p q))
    (f : GammaGroundMap A.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedWeakVFFibreVanishing linear A C f z) :
    ambientBoundedVFVolume e hB hγ linear H (nativeVFClass A) = 0 := by
  change ambientPuiseuxComparison hc e G.base hB hγ (nativeVFBoundedValue linear H (nativeVFClass A)) = 0
  rw [nativeBoundedWeakVFFubini_vanishing linear H A C f h,map_zero]

end DiamondIntegral.Section5.PuiseuxOriginal
