import «section 5».NativeWeakWitnessVFMapTotals
import «section 5».NativeWeakVFMapPartitions
import «section 5».NativeVFFubini
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

theorem nativeBoundedWeakVFFubini
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeBoundedWeakVFFibreLiftEquality G.model00 linear G.uncountable.le
      G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' z) :
    nativeVFBoundedValue linear H (nativeVFClass A) =
      nativeVFBoundedValue linear H (nativeVFClass A') := by
  obtain ⟨N,P,hP,hd,hcov⟩ := native_weak_vf_map_whole_witness_partition G.model00 linear G.uncountable.le
    G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' h
  have hp := nativeMap_preimage_partition f P hd hcov
  have hp' := nativeMap_preimage_partition f' P hd hcov
  let L (i : Fin N) := A.restrict (f.preimage (P i)) (f.preimage_subset (P i))
  let R (i : Fin N) := A'.restrict (f'.preimage (P i)) (f'.preimage_subset (P i))
  have hLclass : nativeVFClass A = ∑ i,nativeVFClass (L i) :=
    nativeVFClass_finite_partition A (fun i => f.preimage (P i)) hp.1 hp.2
  have hRclass : nativeVFClass A' = ∑ i,nativeVFClass (R i) :=
    nativeVFClass_finite_partition A' (fun i => f'.preimage (P i)) hp'.1 hp'.2
  have hL := (congrArg (nativeVFBoundedValue linear H) hLclass).trans (map_sum _ _ _)
  have hR := (congrArg (nativeVFBoundedValue linear H) hRclass).trans (map_sum _ _ _)
  refine hL.trans ((Finset.sum_congr rfl (fun i _ => ?_)).trans hR.symm)
  rcases (hP i).2 with hempty | ⟨W,hW⟩
  · have he (A0 : GammaGroundFiniteVFObject hc G.base) (g : GammaGroundMap A0.domain C) :
        (g.preimage (P i)).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨a,ha,hz⟩
      exact Set.notMem_empty _ (hempty ▸ hz)
    have heL : nativeVFClass (L i) = 0 := nativeVFClass_of_empty (L i) (he A f)
    have heR : nativeVFClass (R i) = 0 := nativeVFClass_of_empty (R i) (he A' f')
    exact (congrArg (nativeVFBoundedValue linear H) heL).trans
      (congrArg (nativeVFBoundedValue linear H) heR).symm
  · exact nativeVFBoundedValue_map_fixed_whole_weak_witness linear H A A' C f f' (P i) W hW

end DiamondIntegral.Section5
