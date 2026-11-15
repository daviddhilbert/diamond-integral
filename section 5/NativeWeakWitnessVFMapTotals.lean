import «section 5».NativeWeakFixedWitnessVFFubini
import «section 5».NativeWitnessVFMapTotals
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
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {G : GammaGroundContext M}

theorem nativeVFBoundedValue_map_fixed_whole_weak_witness
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (W : NativeVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc .bounded
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val)
    (hW : ∀ b : Z,W.ValidWeak hc (nativeMixedCode b.val)) :
    nativeVFBoundedValue linear H (nativeVFClass (A.restrict (f.preimage Z) (f.preimage_subset Z))) =
      nativeVFBoundedValue linear H (nativeVFClass (A'.restrict (f'.preimage Z) (f'.preimage_subset Z))) := by
  have hWr : ∀ z ∈ nativeMixedDomain Z,W.ValidWeak hc z := by
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
  have he := native_vf_fixed_whole_witness_fubini_weak linear H Z W hW hfL hfR
  exact (congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection _ L eL)).trans
    (he.trans (congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection _ R eR)).symm)

end DiamondIntegral.Section5
