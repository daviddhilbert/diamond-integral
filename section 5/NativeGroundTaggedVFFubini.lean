import «section 5».VFAdjoinedMixedFibreValues
import «section 5».NativeGroundRVLabels

/-! Finite original-field RV tags in chart encodings do not alter the
intrinsic F(b) hypothesis. This version covers native finite coproducts. -/
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

variable {p q : ℕ}

theorem nativeGroundRVLabels_raw
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)) (hC : NativeGroundRVLabels C)
    (z : Fin (p+q) → M) (hz : z ∈ nativeMixedDomain C) :
    ∀ i,iRV (z i) → z i ∈ G.base.real := by
  obtain ⟨a,ha,rfl⟩ := hz
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hj
    have hv : iVF (nativeMixedCode a (Fin.castAdd q j)) := by
      simpa only [nativeMixedCode,Fin.append_left,vfValues] using (a.1 j).property
    exact (TypedModelMap.not_rv_of_vf hv hj).elim
  · intro _
    simpa only [nativeMixedCode,Fin.append_right,rvValues] using hC ⟨a,ha⟩ j

theorem nativeBoundedVFFubini_ground_tagged_vanishing
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (A : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)) (hC : NativeGroundRVLabels C)
    (f : GammaGroundMap A.domain C)
    (I : ∀ z : Fin (p+q) → M, (∀ i,iRV (z i) → z i ∈ G.base.real) →
      YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G z hnt) hc)
    (h : ∀ z (hz : z ∈ nativeMixedDomain C),
      nativeVFBoundedValue linear (I z (nativeGroundRVLabels_raw C hC z hz))
        (nativeVFClass (vfAdjoinedMixedFiniteObject z (nativeGroundRVLabels_raw C hC z hz) hnt hγ (nativeFiniteMixedMapFibre A f z))) = 0) :
    nativeVFBoundedValue linear H (nativeVFClass A) = 0 := by
  apply nativeBoundedWeakVFFubini_vanishing linear H A C f
  intro z hz
  let hb := nativeGroundRVLabels_raw C hC z hz
  let J := vfRawMixedParameterLiftInput hc G z hb hnt hγ (I z hb)
  have hr : originalBaseVFBoundedValue (hc := hc) (B := vfRawParameterBase G z) G.model00 linear G.uncountable.le G.saturated
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
      (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J
      (nativeVFClass (nativeFiniteMixedMapFibre A f z)) = 0 :=
    vfAdjoinedMixedFibreValue_to_raw linear z hb hnt hγ (I z hb) (nativeFiniteMixedMapFibre A f z) (h z hz)
  obtain ⟨k,U,⟨e⟩,hv⟩ := originalBaseVFBoundedValue_positive_presentation (hc := hc) (B := vfRawParameterBase G z)
    G.model00 linear G.uncountable G.saturated
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
    (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J (nativeFiniteMixedMapFibre A f z)
  exact ⟨k,U,⟨e⟩,hv.symm.trans hr⟩

end DiamondIntegral.Section5
