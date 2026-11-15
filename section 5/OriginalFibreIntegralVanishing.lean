import «section 5».OriginalBaseWeakVFValues
import «section 5».NativeWeakVFFubiniVanishing

/-! The bounded Fubini vanishing hypothesis can be stated directly for
the intrinsic Section 3 fibre integral, using the exact original real
parameters and the original Gamma ground. The positive lift hypothesis
is deduced by actual original-ground preparation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {p q : ℕ}

def nativeFiniteMixedMapFibre (A : GammaGroundFiniteVFObject hc G.base)
    {C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)}
    (f : GammaGroundMap A.domain C) (z : Fin (p+q) → M) :
    GammaGroundFiniteVFObject hc ⟨G.base.real ∪ Set.range z,G.base.gamma⟩ :=
  ⟨A.vfArity,A.rvArity,nativeMixedMapFibreAt f z,nativeMixedMapFibreAt_finite f A.finite z⟩

theorem nativeBoundedVFFubini_intrinsic_fibre_vanishing
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C)
    (Hz : ∀ z : Fin (p+q) → M,OriginalBaseUnmeasuredLiftInput hc ⟨G.base.real ∪ Set.range z,G.base.gamma⟩)
    (h : ∀ z ∈ nativeMixedDomain C,
      originalBaseVFBoundedValue (hc := hc) (B := ⟨G.base.real ∪ Set.range z,G.base.gamma⟩) G.model00 linear G.uncountable.le G.saturated
        (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
        (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) (Hz z)
          (nativeVFClass (nativeFiniteMixedMapFibre A f z)) = 0) :
    nativeVFBoundedValue linear H (nativeVFClass A) = 0 := by
  apply nativeBoundedWeakVFFubini_vanishing linear H A C f
  intro z hz
  obtain ⟨k,U,⟨e⟩,hv⟩ := originalBaseVFBoundedValue_positive_presentation (hc := hc) (B := ⟨G.base.real ∪ Set.range z,G.base.gamma⟩) G.model00 linear G.uncountable
    G.saturated (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
    (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) (Hz z)
    (nativeFiniteMixedMapFibre A f z)
  exact ⟨k,U,⟨e⟩,hv.symm.trans (h z hz)⟩

end DiamondIntegral.Section5
