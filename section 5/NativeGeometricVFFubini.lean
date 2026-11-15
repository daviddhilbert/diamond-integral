import «section 5».NativeFixedGeometricWitnessVFFubini
import «section 5».NativeGeometricVFMapWitnesses
import «section 5».NativeWitnessVFMapTotals
import «section 5».NativeVFFubini

/-! The approved geometric version of Theorem 5.17 for actual native VF
maps. Fibre equality is in the intrinsic ungraded affine localization.
Finite denominator witnesses are uniformized before preparation; each
base zero stratum is normalized in its common total degree. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

theorem nativeVFGeometricValue_map_fixed_whole_witness
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (W : NativeGeometricVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val)
    (hW : ∀ b : Z,W.Valid (nativeMixedCode b.val)) :
    nativeVFGeometricValue linear H (nativeVFClass (A.restrict (f.preimage Z) (f.preimage_subset Z))) =
      nativeVFGeometricValue linear H (nativeVFClass (A'.restrict (f'.preimage Z) (f'.preimage_subset Z))) := by
  have hWr : ∀ z ∈ nativeMixedDomain Z,W.Valid z := by
    rintro z ⟨b,hb,he⟩
    exact he ▸ hW ⟨b,hb⟩
  have hL := fun z hz => (hWr z hz).2.2.1
  have hR := fun z hz => (hWr z hz).2.2.2.1
  let eL := nativeVFMapLiftWitnessBijection f Z W.leftRV W.leftLift hL
  let eR := nativeVFMapLiftWitnessBijection f' Z W.rightRV W.rightLift hR
  have hfL := nativeVFMapLiftWitness_finite G.uncountable.le G.saturated G.model00 G.small_real
    f Z W.leftRV W.leftLift hL A.finite
  have hfR := nativeVFMapLiftWitness_finite G.uncountable.le G.saturated G.model00 G.small_real
    f' Z W.rightRV W.rightLift hR A'.finite
  let L : GammaGroundFiniteVFObject hc G.base :=
    ⟨p+W.leftDegree,q+W.leftArity,nativeVFLiftFamily Z W.leftRV,hfL⟩
  let R : GammaGroundFiniteVFObject hc G.base :=
    ⟨p+W.rightDegree,q+W.rightArity,nativeVFLiftFamily Z W.rightRV,hfR⟩
  have he := native_vf_fixed_geometric_whole_witness_fubini linear H Z W hW hfL hfR
  exact (congrArg (nativeVFGeometricValue linear H) (nativeVFClass_bijection _ L eL)).trans
    (he.trans (congrArg (nativeVFGeometricValue linear H) (nativeVFClass_bijection _ R eR)).symm)


theorem nativeGeometricVFFubini
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z ∈ nativeMixedDomain C,NativeGeometricVFFibreLiftEquality G.model00 linear G.uncountable.le
      G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' z) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      nativeVFGeometricValue linear H (nativeVFClass A') := by
  obtain ⟨N,P,hP,hd,hcov⟩ := native_geometric_vf_map_whole_witness_partition G.model00 linear G.uncountable.le
    G.saturated G.small_real G.small_gamma G.nontrivial_definable_gamma f f' h
  have hp := nativeMap_preimage_partition f P hd hcov
  have hp' := nativeMap_preimage_partition f' P hd hcov
  let L (i : Fin N) := A.restrict (f.preimage (P i)) (f.preimage_subset (P i))
  let R (i : Fin N) := A'.restrict (f'.preimage (P i)) (f'.preimage_subset (P i))
  have hLclass : nativeVFClass A = ∑ i,nativeVFClass (L i) :=
    nativeVFClass_finite_partition A (fun i => f.preimage (P i)) hp.1 hp.2
  have hRclass : nativeVFClass A' = ∑ i,nativeVFClass (R i) :=
    nativeVFClass_finite_partition A' (fun i => f'.preimage (P i)) hp'.1 hp'.2
  have hL := (congrArg (nativeVFGeometricValue linear H) hLclass).trans (map_sum _ _ _)
  have hR := (congrArg (nativeVFGeometricValue linear H) hRclass).trans (map_sum _ _ _)
  refine hL.trans ((Finset.sum_congr rfl (fun i _ => ?_)).trans hR.symm)
  rcases (hP i).2 with hempty | ⟨W,hW⟩
  · have he (A0 : GammaGroundFiniteVFObject hc G.base) (g : GammaGroundMap A0.domain C) :
        (g.preimage (P i)).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨a,ha,hz⟩
      exact Set.notMem_empty _ (hempty ▸ hz)
    have heL : nativeVFClass (L i) = 0 := nativeVFClass_of_empty (L i) (he A f)
    have heR : nativeVFClass (R i) = 0 := nativeVFClass_of_empty (R i) (he A' f')
    exact (congrArg (nativeVFGeometricValue linear H) heL).trans
      (congrArg (nativeVFGeometricValue linear H) heR).symm
  · exact nativeVFGeometricValue_map_fixed_whole_witness linear H A A' C f f' (P i) W hW


end DiamondIntegral.Section5
