import «section 5».NativeMixedGraphBridge
import IntegrationSection6.GammaSortedTotalBijections

/-! Actual mixed native maps retain their complete original-base
graphs in sorted tuple coordinates. This supplies the geometric input
for original-language promotion of VF fibre lift witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s : ℕ}

def nativeMixedMapGraph
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundMap A C) : Set (Fin ((n+r)+(m+s)) → M) :=
  {w | ∃ u : A, w = Fin.append (nativeMixedCode u.val) (nativeMixedCode (f u).val)}

theorem nativeMixedMapGraph_definable
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundMap A C) :
    DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
        (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) (nativeMixedMapGraph f) := by
  have h := f.graph_definable.on_real_codes.image_comp (nativeMixedPairCodeIndices n r m s)
  have he : (fun z => z ∘ nativeMixedPairCodeIndices n r m s) ''
      ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)).preimage
        {q | ∃ u : A, u.val = q.1 ∧ (f u).val = q.2} = nativeMixedMapGraph f := by
    ext w
    constructor
    · rintro ⟨z,⟨hz,u,hu,hv⟩,rfl⟩
      refine ⟨u,?_⟩
      have hcode := nativeMixedPairCode_decode (M := M) (n := n) (r := r) (m := m) (s := s) ⟨z,hz⟩
      rw [←hu,←hv] at hcode
      exact hcode.symm
    · rintro ⟨u,rfl⟩
      obtain ⟨c,hc⟩ := ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)).onto (u.val,(f u).val)
      refine ⟨c.val,⟨c.property,u,(congrArg Prod.fst hc).symm,(congrArg Prod.snd hc).symm⟩,?_⟩
      exact (nativeMixedPairCode_decode c).symm.trans
        (congrArg (fun q => Fin.append (nativeMixedCode q.1) (nativeMixedCode q.2)) hc)
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) ?_).mp
  · exact h.congr (fun w => Set.ext_iff.mp he w)
  · rintro w ⟨u,rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using nativeMixedCode_proper u.val j
    · simpa only [Fin.append_right] using nativeMixedCode_proper (f u).val j


end DiamondIntegral.Section5
