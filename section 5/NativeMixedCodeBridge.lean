import «section 4».Section3RVCodeBridge
import «section 3».GammaGroundFiniteVFObjects

/-! Literal VF/RV tuple codes retain the exact original Gamma ground.
Actual mixed native domains therefore have full sorted original-language
formulas suitable for promoting fibre VF lift graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def nativeMixedCode (q : Section2.Mixed M n r) : Fin (n+r) → M :=
  Fin.append (vfValues q.1) (rvValues q.2)

theorem nativeMixedCode_injective : Function.Injective (nativeMixedCode (M := M) (n := n) (r := r)) := by
  intro q q' h
  apply Prod.ext
  · apply vfValues_injective
    funext i
    have hi := congrFun h (Fin.castAdd r i)
    simpa only [nativeMixedCode,Fin.append_left] using hi
  · apply rvValues_injective
    funext i
    have hi := congrFun h (Fin.natAdd n i)
    simpa only [nativeMixedCode,Fin.append_right] using hi

theorem nativeMixedCode_proper (q : Section2.Mixed M n r) :
    nativeMixedCode q ∈ sortedUniverse (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv)) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [nativeMixedCode,Fin.append_left,sortEval,iVF,vfValues] using (q.1 j).property
  · simpa only [nativeMixedCode,Fin.append_right,sortEval,iRV,rvValues] using (q.2 j).property

def nativeMixedCodeIndices (n r : ℕ) : Fin (n+r) → Fin n ⊕ Fin r := Fin.addCases Sum.inl Sum.inr

theorem nativeMixedCode_decode (c : (rawMixedSpace (M := M) n r).domain) :
    nativeMixedCode ((rawMixedSpace n r).decode c) = c.val ∘ nativeMixedCodeIndices n r := by
  have hx : vfValues ((rawMixedSpace n r).decode c).1 = c.val ∘ Sum.inl :=
    Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace (M := M) n).domain_definable
      ⟨c.val ∘ Sum.inl,c.property.1⟩
  have hy : rvValues ((rawMixedSpace n r).decode c).2 = c.val ∘ Sum.inr :=
    rvValues_decode ⟨c.val ∘ Sum.inr,c.property.2⟩
  unfold nativeMixedCode
  rw [hx,hy]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [nativeMixedCodeIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def nativeMixedDomain (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) : Set (Fin (n+r) → M) :=
  nativeMixedCode '' A.carrier

theorem nativeMixedDomain_definable (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    DefinableOverBase B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv)) (nativeMixedDomain A) := by
  have h := A.definable.on_real_codes.image_comp (nativeMixedCodeIndices n r)
  have he : (fun z => z ∘ nativeMixedCodeIndices n r) '' (rawMixedSpace (M := M) n r).preimage A.carrier =
      nativeMixedDomain A := by
    ext w
    constructor
    · rintro ⟨z,⟨hz,ha⟩,rfl⟩
      exact ⟨(rawMixedSpace n r).decode ⟨z,hz⟩,ha,nativeMixedCode_decode ⟨z,hz⟩⟩
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨c,hc⟩ := (rawMixedSpace n r).onto q
      refine ⟨c.val,⟨c.property,?_⟩,?_⟩
      · exact hc.symm ▸ hq
      · exact (nativeMixedCode_decode c).symm.trans (congrArg nativeMixedCode hc)
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) ?_).mp
  · exact h.congr (fun w => Set.ext_iff.mp he w)
  · rintro w ⟨q,hq,rfl⟩
    exact nativeMixedCode_proper q

def nativeMixedDomainEquiv (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    A ≃ nativeMixedDomain A :=
  Equiv.ofBijective (fun q => ⟨nativeMixedCode q.val,⟨q.val,q.property,rfl⟩⟩)
    ⟨fun q q' h => Subtype.ext (nativeMixedCode_injective (congrArg Subtype.val h)),by
      rintro ⟨w,q,hq,rfl⟩
      exact ⟨⟨q,hq⟩,rfl⟩⟩

end DiamondIntegral.Section5
