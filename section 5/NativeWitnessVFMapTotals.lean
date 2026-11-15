import «section 5».NativeMixedPartialTotals
import «section 5».NativeFixedWitnessVFFubini

/-! Whole fibre lift graphs assemble actual original-ground bijections
from a source preimage to the literal RV lift family. The fixed-witness
VF Fubini theorem therefore compares actual map preimages. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q n r a k : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}

def nativeVFMapLiftWitnessBijection (f : GammaGroundMap A C)
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (L : GammaSortedBijectionChart B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin k => .vf) (fun _ : Fin a => .rv)))
    (hL : ∀ z ∈ nativeMixedDomain Z,L.valid (nativeMixedMapFibreFormula f).val (finiteRVSchemaLiftDomain hc F).val z) :
    GammaGroundBijection (f.preimage Z) (nativeVFLiftFamily Z F) :=
  (nativeMixedFamilyTotalBijection (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
    (nativeMixedMapFibreFormula f).val (finiteRVSchemaLiftDomain hc F).val
    (nativeMixedMapFibreFormula f).property (finiteRVSchemaLiftDomain hc F).property L hL).comp
    (nativeMixedPartialTotalBijection f Z)

theorem nativeVFMapLiftWitness_finite
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (f : GammaGroundMap A C) (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (L : GammaSortedBijectionChart B (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin k => .vf) (fun _ : Fin a => .rv)))
    (hL : ∀ z ∈ nativeMixedDomain Z,L.valid (nativeMixedMapFibreFormula f).val (finiteRVSchemaLiftDomain hc F).val z)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite :=
  (gammaGroundFiniteRVFibres_iff (nativeVFMapLiftWitnessBijection f Z F L hL) hκ hs h00 hr).mp
    (fun x => (hf x).subset (fun _ ht => f.preimage_subset Z ht))

variable {G : GammaGroundContext M}

theorem nativeVFBoundedValue_map_fixed_whole_witness
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (W : NativeVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc .bounded
        (nativeMixedMapFibreFormula f).val (nativeMixedMapFibreFormula f').val)
    (hW : ∀ b : Z,W.Valid hc (nativeMixedCode b.val)) :
    nativeVFBoundedValue linear H (nativeVFClass (A.restrict (f.preimage Z) (f.preimage_subset Z))) =
      nativeVFBoundedValue linear H (nativeVFClass (A'.restrict (f'.preimage Z) (f'.preimage_subset Z))) := by
  have hWr : ∀ z ∈ nativeMixedDomain Z,W.Valid hc z := by
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
  have he := native_vf_fixed_whole_witness_fubini linear H Z W hW hfL hfR
  exact (congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection _ L eL)).trans
    (he.trans (congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection _ R eR)).symm)

end DiamondIntegral.Section5
