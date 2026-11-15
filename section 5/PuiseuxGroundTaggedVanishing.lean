import «section 5».NativeGroundTaggedVFFubini
import «section 5».PuiseuxLaurentNontrivial
import «section 5».PuiseuxAmbientWeakVanishing

/-! The actual Laurent-base ambient comparison vanishes for a VF-tuple
map whenever its genuine F(b) intrinsic fibre integrals vanish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance groundTaggedVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance groundTaggedVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := N)} {G : GammaGroundContext N}

theorem ambientBoundedVFVolume_ground_tagged_fibres
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := N) p q)) (hC : NativeGroundRVLabels C)
    (f : GammaGroundMap A.domain C)
    (I : ∀ z : Fin (p+q) → N, (∀ i,iRV (z i) → z i ∈ G.base.real) → YinGammaGroundUnmeasuredLiftInput
      (vfAdjoinedContext hc G z (ambientLaurentField_nontrivial e G hB)) hc)
    (h : ∀ z (hz : z ∈ nativeMixedDomain C),
      nativeVFBoundedValue linear (I z (nativeGroundRVLabels_raw C hC z hz))
        (nativeVFClass (vfAdjoinedMixedFiniteObject z (nativeGroundRVLabels_raw C hC z hz)
          (ambientLaurentField_nontrivial e G hB) hγ (nativeFiniteMixedMapFibre A f z))) = 0) :
    ambientBoundedVFVolume e hB hγ linear H (nativeVFClass A) = 0 := by
  change ambientPuiseuxComparison hc e G.base hB hγ (nativeVFBoundedValue linear H (nativeVFClass A)) = 0
  rw [nativeBoundedVFFubini_ground_tagged_vanishing linear H (ambientLaurentField_nontrivial e G hB) hγ A C hC f I h,map_zero]

end DiamondIntegral.Section5.PuiseuxOriginal
