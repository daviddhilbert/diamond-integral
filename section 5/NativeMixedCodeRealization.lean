import «section 5».NativeMixedCodeBridge

/-! Every proper literal VF/RV code is an actual mixed point. This
identifies complete sorted row formulas with actual native fibre domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def nativeMixedPointOfCode (w : Fin (n+r) → M)
    (hw : w ∈ sortedUniverse (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) :
    Section2.Mixed M n r :=
  (fun i => ⟨w (Fin.castAdd r i),by simpa only [Fin.append_left,sortEval,iVF] using hw (Fin.castAdd r i)⟩,
    fun i => ⟨w (Fin.natAdd n i),by simpa only [Fin.append_right,sortEval,iRV] using hw (Fin.natAdd n i)⟩)

theorem nativeMixedPointOfCode_code (w : Fin (n+r) → M)
    (hw : w ∈ sortedUniverse (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) :
    nativeMixedCode (nativeMixedPointOfCode w hw) = w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [nativeMixedCode,nativeMixedPointOfCode,Fin.append_left,Fin.append_right,vfValues,rvValues]

theorem nativeMixedDomain_mem_iff
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (w : Fin (n+r) → M)
    (hw : w ∈ sortedUniverse (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) :
    w ∈ nativeMixedDomain A ↔ nativeMixedPointOfCode w hw ∈ A.carrier := by
  constructor
  · rintro ⟨q,hq,hcode⟩
    have he : q = nativeMixedPointOfCode w hw :=
      nativeMixedCode_injective (hcode.trans (nativeMixedPointOfCode_code w hw).symm)
    exact he ▸ hq
  · intro h
    exact ⟨nativeMixedPointOfCode w hw,h,nativeMixedPointOfCode_code w hw⟩

end DiamondIntegral.Section5
