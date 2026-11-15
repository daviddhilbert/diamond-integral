import «section 5».PuiseuxAmbientWeakVanishing
import «section 5».OriginalFibreIntegralVanishing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance ambientIntrinsicVanishingSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientIntrinsicVanishingSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := N)} {G : GammaGroundContext N}

theorem ambientBoundedVFVolume_intrinsic_fibre_vanishing
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := N) p q))
    (f : GammaGroundMap A.domain C)
    (Hz : ∀ z : Fin (p+q) → N,OriginalBaseUnmeasuredLiftInput hc ⟨G.base.real ∪ Set.range z,G.base.gamma⟩)
    (h : ∀ z ∈ nativeMixedDomain C,
      originalBaseVFBoundedValue (hc := hc) (B := ⟨G.base.real ∪ Set.range z,G.base.gamma⟩) G.model00 linear G.uncountable.le G.saturated
        (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
        (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) (Hz z)
          (nativeVFClass (nativeFiniteMixedMapFibre A f z)) = 0) :
    ambientBoundedVFVolume e hB hγ linear H (nativeVFClass A) = 0 := by
  change ambientPuiseuxComparison hc e G.base hB hγ (nativeVFBoundedValue linear H (nativeVFClass A)) = 0
  rw [nativeBoundedVFFubini_intrinsic_fibre_vanishing linear H A C f Hz h,map_zero]

end DiamondIntegral.Section5.PuiseuxOriginal
