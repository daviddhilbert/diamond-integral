import «section 5».NativeVFFubini
import «section 3».GammaGroundFiniteGluing

/-! Fibrewise intrinsic bounded vanishing implies actual VF total
vanishing. Applying any ground comparison preserves the conclusion;
no fibre comparison or base-extension injectivity is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M} {p q : ℕ}

def NativeBoundedVFFibreLiftVanishing
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (A : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (z : Fin (p+q) → M) : Prop :=
  ∃ k : ℕ,∃ U : GammaGroundRVObject hc ⟨G.base.real ∪ Set.range z,G.base.gamma⟩ k,
    Nonempty (GammaGroundBijection (nativeMixedMapFibreAt f z) (gammaGroundObjectLift U)) ∧
      nativeRVEvaluation G.model00 linear G.uncountable.le G.saturated hc
        ⟨G.base.real ∪ Set.range z,G.base.gamma⟩
        (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
        (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) .bounded
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) = 0

theorem nativeBoundedVFFubini_vanishing
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedVFFibreLiftVanishing linear A C f z) :
    nativeVFBoundedValue linear H (nativeVFClass A) = 0 := by
  let E := GammaGroundFiniteVFObject.empty hc G.base
  let f0 : GammaGroundMap E.domain C := GammaGroundMap.emptyTo C
  have he := nativeBoundedVFFubini linear H A E C f f0 (by
    intro z hz
    obtain ⟨k,U,⟨eU⟩,hU⟩ := h z hz
    let V := GammaGroundRVObject.empty hc (⟨G.base.real ∪ Set.range z,G.base.gamma⟩ : Base (M := M)) 0
    have hF : (nativeMixedMapFibreAt f0 z).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨a,_,_⟩ := (nativeMixedMapFibreAt_mem f0 z x).mp hx
      exact a.property
    have hV : (gammaGroundObjectLift V).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨u,_,_⟩
      exact u.property
    refine ⟨k,0,U,V,⟨eU⟩,⟨GammaGroundBijection.ofEmpty hF hV⟩,?_⟩
    refine hU.trans ?_
    symm
    rw [←nativeGroundRVEvaluation_class]
    change nativeGroundRVEvaluation G.model00 linear G.uncountable.le G.saturated hc
      ⟨G.base.real ∪ Set.range z,G.base.gamma⟩
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real z) G.small_gamma
      (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) .bounded
      (ordinaryClass V) = 0
    rw [ordinary_empty,map_zero])
  exact he.trans (by rw [nativeVFClass_of_empty E rfl,map_zero])

theorem nativeBoundedVFFubini_vanishing_map
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedVFFibreLiftVanishing linear A C f z)
    {R : Type*} [CommRing R] (Θ : RESDimensionFreeReduction.Ring G.base →+* R) :
    Θ (nativeVFBoundedValue linear H (nativeVFClass A)) = 0 := by
  rw [nativeBoundedVFFubini_vanishing linear H A C f h,map_zero]

end DiamondIntegral.Section5
