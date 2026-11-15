import «section 5».VFAdjoinedFibreValues

/-! The final vanishing statement for actual VF-tuple maps uses intrinsic
integrals over the genuine generated fields F(b). The exact parameter
presentation and all positive fibre lifts are proved constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

theorem nativePureVFTuple_proper {n : ℕ}
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) n 0))
    (z : Fin n → M) (hz : z ∈ nativeMixedDomain C) : ∀ i,iVF (z i) := by
  intro i
  have h := (nativeMixedDomain_definable C).proper z hz (Fin.castAdd 0 i)
  have h' : iVF (z (Fin.castAdd 0 i)) := by simpa only [Fin.append_left,sortEval,iVF] using h
  have hi : Fin.castAdd 0 i = i := Fin.ext rfl
  exact (congrArg (fun j => iVF (z j)) hi).mp h'

theorem nativeBoundedVFFubini_field_generated_vanishing
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p 0))
    (f : GammaGroundMap A.domain C)
    (I : ∀ z : Fin p → M, (∀ i,iVF (z i)) → YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G z hnt) hc)
    (h : ∀ z (hz : z ∈ nativeMixedDomain C),
      nativeVFBoundedValue linear (I z (nativePureVFTuple_proper C z hz))
        (nativeVFClass (vfAdjoinedFiniteObject z (nativePureVFTuple_proper C z hz) hnt hγ (nativeFiniteMixedMapFibre A f z))) = 0) :
    nativeVFBoundedValue linear H (nativeVFClass A) = 0 := by
  apply nativeBoundedWeakVFFubini_vanishing linear H A C f
  intro z hz
  let hb := nativePureVFTuple_proper C z hz
  let J := vfRawParameterLiftInput hc G z hb hnt hγ (I z hb)
  have hr : originalBaseVFBoundedValue (hc := hc) (B := vfRawParameterBase G z) G.model00 linear G.uncountable.le G.saturated
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
      (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J
      (nativeVFClass (nativeFiniteMixedMapFibre A f z)) = 0 :=
    vfAdjoinedFibreValue_to_raw linear z hb hnt hγ (I z hb) (nativeFiniteMixedMapFibre A f z) (h z hz)
  obtain ⟨k,U,⟨e⟩,hv⟩ := originalBaseVFBoundedValue_positive_presentation (hc := hc) (B := vfRawParameterBase G z)
    G.model00 linear G.uncountable G.saturated
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
    (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J (nativeFiniteMixedMapFibre A f z)
  exact ⟨k,U,⟨e⟩,hv.symm.trans hr⟩

end DiamondIntegral.Section5
