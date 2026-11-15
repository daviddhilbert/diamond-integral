import «section 5».NativeMixedCodeBridge
import IntegrationSection6.GammaSortedTotalBijections

/-! Actual mixed native bijections retain their complete original-base
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

def nativeMixedPairCodeIndices (n r m s : ℕ) :
    Fin ((n+r)+(m+s)) → (Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s) :=
  Fin.addCases (fun i => Sum.inl (nativeMixedCodeIndices n r i)) (fun i => Sum.inr (nativeMixedCodeIndices m s i))

theorem nativeMixedPairCode_decode
    (c : ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)).domain) :
    Fin.append (nativeMixedCode (((rawMixedSpace n r).prod (rawMixedSpace m s)).decode c).1)
      (nativeMixedCode (((rawMixedSpace n r).prod (rawMixedSpace m s)).decode c).2) =
      c.val ∘ nativeMixedPairCodeIndices n r m s := by
  have hx := nativeMixedCode_decode (M := M) (n := n) (r := r) ⟨c.val ∘ Sum.inl,c.property.1⟩
  have hy := nativeMixedCode_decode (M := M) (n := m) (r := s) ⟨c.val ∘ Sum.inr,c.property.2⟩
  change Fin.append (nativeMixedCode ((rawMixedSpace n r).decode ⟨c.val ∘ Sum.inl,c.property.1⟩))
    (nativeMixedCode ((rawMixedSpace m s).decode ⟨c.val ∘ Sum.inr,c.property.2⟩)) = _
  rw [hx,hy]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [nativeMixedPairCodeIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def nativeMixedGraph
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection A C) : Set (Fin ((n+r)+(m+s)) → M) :=
  {w | ∃ u : A, w = Fin.append (nativeMixedCode u.val) (nativeMixedCode (f.map u).val)}

theorem nativeMixedGraph_definable
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection A C) :
    DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
        (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) (nativeMixedGraph f) := by
  have h := f.map.graph_definable.on_real_codes.image_comp (nativeMixedPairCodeIndices n r m s)
  have he : (fun z => z ∘ nativeMixedPairCodeIndices n r m s) ''
      ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)).preimage
        {q | ∃ u : A, u.val = q.1 ∧ (f.map u).val = q.2} = nativeMixedGraph f := by
    ext w
    constructor
    · rintro ⟨z,⟨hz,u,hu,hv⟩,rfl⟩
      refine ⟨u,?_⟩
      have hcode := nativeMixedPairCode_decode (M := M) (n := n) (r := r) (m := m) (s := s) ⟨z,hz⟩
      rw [←hu,←hv] at hcode
      exact hcode.symm
    · rintro ⟨u,rfl⟩
      obtain ⟨c,hc⟩ := ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)).onto (u.val,(f.map u).val)
      refine ⟨c.val,⟨c.property,u,(congrArg Prod.fst hc).symm,(congrArg Prod.snd hc).symm⟩,?_⟩
      exact (nativeMixedPairCode_decode c).symm.trans
        (congrArg (fun q => Fin.append (nativeMixedCode q.1) (nativeMixedCode q.2)) hc)
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) ?_).mp
  · exact h.congr (fun w => Set.ext_iff.mp he w)
  · rintro w ⟨u,rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using nativeMixedCode_proper u.val j
    · simpa only [Fin.append_right] using nativeMixedCode_proper (f.map u).val j

def nativeMixedSortedIso
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection A C) :
    GammaSortedIso B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv)) (nativeMixedDomain A) (nativeMixedDomain C) := by
  let P := nativeMixedDomainEquiv A
  let Q := nativeMixedDomainEquiv C
  let e := P.symm.trans ((Equiv.ofBijective f.map f.bijective).trans Q)
  refine ⟨e,?_⟩
  convert nativeMixedGraph_definable f using 1
  ext w
  constructor
  · rintro ⟨u,hu⟩
    let x := P.symm u
    have hx : nativeMixedCode x.val = u.val := congrArg Subtype.val (P.apply_symm_apply u)
    exact ⟨x,hu.symm.trans (congrArg₂ Fin.append hx.symm rfl)⟩
  · rintro ⟨u,rfl⟩
    refine ⟨P u,?_⟩
    change Fin.append (nativeMixedCode u.val) (nativeMixedCode (f.map (P.symm (P u))).val) = _
    rw [P.symm_apply_apply]

end DiamondIntegral.Section5
