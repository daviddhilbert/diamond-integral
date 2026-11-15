import «section 5».NativeMixedCodeRealization
import «section 5».NativeMixedGraphBridge

/-! Sorted original-language mixed domains and full bijection graphs
realize actual native Gamma-ground domains and bijections, retaining the
same real and Gamma parameters. -/
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

def nativeMixedOfRaw (D : Set (Fin (n+r) → M))
    (hD : DefinableOverBase B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv)) D) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) n r) where
  carrier := {q | nativeMixedCode q ∈ D}
  definable := by
    have hraw := ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hD.proper).mpr hD).preimage_comp
      (nativeMixedCodeIndices n r)
    have hdom : GammaGroundRawDefinable hc B (rawMixedSpace (M := M) n r).domain :=
      GammaGroundRawDefinable.of_real ((rawMixedSpace n r).domain_definable.mono (Set.empty_subset B.real))
    apply GammaGroundDefinable.of_real_codes
    apply (hdom.inter hraw).congr
    intro z
    constructor
    · rintro ⟨hz,hd⟩
      refine ⟨hz,?_⟩
      change nativeMixedCode ((rawMixedSpace n r).decode ⟨z,hz⟩) ∈ D
      rw [nativeMixedCode_decode]
      exact hd
    · rintro ⟨hz,hd⟩
      refine ⟨hz,?_⟩
      change nativeMixedCode ((rawMixedSpace n r).decode ⟨z,hz⟩) ∈ D at hd
      rw [nativeMixedCode_decode] at hd
      exact hd

theorem nativeMixedDomain_ofRaw (D : Set (Fin (n+r) → M))
    (hD : DefinableOverBase B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv)) D) :
    nativeMixedDomain (nativeMixedOfRaw (hc := hc) D hD) = D := by
  ext w
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact hq
  · intro hw
    let q := nativeMixedPointOfCode w (hD.proper w hw)
    have hq : nativeMixedCode q = w := nativeMixedPointOfCode_code w (hD.proper w hw)
    have hmem : q ∈ (nativeMixedOfRaw (hc := hc) D hD).carrier := by
      change nativeMixedCode q ∈ D
      rw [hq]
      exact hw
    exact ⟨q,hmem,hq⟩

def nativeMixedBijectionOfSortedIso
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s))
    (H : GammaSortedIso B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv)) (nativeMixedDomain A) (nativeMixedDomain C)) :
    GammaGroundBijection A C := by
  let P := nativeMixedDomainEquiv A
  let Q := nativeMixedDomainEquiv C
  let e := P.trans (H.equiv.trans Q.symm)
  have heGraph (q : Section2.Mixed M n r × Section2.Mixed M m s) :
      (∃ u : nativeMixedDomain A,
        Fin.append u.val (H.equiv u).val = Fin.append (nativeMixedCode q.1) (nativeMixedCode q.2)) ↔
      ∃ a : A, a.val = q.1 ∧ (e a).val = q.2 := by
    constructor
    · rintro ⟨u,hu⟩
      let a := P.symm u
      have hsrc : u.val = nativeMixedCode q.1 := funext (fun i => by
        have hi := congrFun hu (Fin.castAdd (m+s) i)
        simpa only [Fin.append_left] using hi)
      have htgt : (H.equiv u).val = nativeMixedCode q.2 := funext (fun i => by
        have hi := congrFun hu (Fin.natAdd (n+r) i)
        simpa only [Fin.append_right] using hi)
      refine ⟨a,nativeMixedCode_injective ((congrArg Subtype.val (P.apply_symm_apply u)).trans hsrc),?_⟩
      apply nativeMixedCode_injective
      have he : e a = Q.symm (H.equiv u) := by
        change Q.symm (H.equiv (P (P.symm u))) = _
        rw [P.apply_symm_apply]
      rw [he]
      exact (congrArg Subtype.val (Q.apply_symm_apply (H.equiv u))).trans htgt
    · rintro ⟨a,ha,hb⟩
      refine ⟨P a,?_⟩
      have ht : (H.equiv (P a)).val = nativeMixedCode (e a).val :=
        (congrArg Subtype.val (Q.apply_symm_apply (H.equiv (P a)))).symm
      change Fin.append (nativeMixedCode a.val) (H.equiv (P a)).val = _
      rw [ht,ha,hb]
  refine ⟨⟨e,?_⟩,e.bijective⟩
  have hraw := ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) H.graph.proper).mpr
    H.graph).preimage_comp (nativeMixedPairCodeIndices n r m s)
  let Z := (rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)
  have hdom : GammaGroundRawDefinable hc B Z.domain :=
    GammaGroundRawDefinable.of_real (Z.domain_definable.mono (Set.empty_subset B.real))
  apply GammaGroundDefinable.of_real_codes
  apply (hdom.inter hraw).congr
  intro z
  constructor
  · rintro ⟨hz,hg⟩
    refine ⟨hz,?_⟩
    apply (heGraph (Z.decode ⟨z,hz⟩)).mp
    obtain ⟨u,hu⟩ := hg
    exact ⟨u,hu.trans (nativeMixedPairCode_decode (n := n) (r := r) (m := m) (s := s) ⟨z,hz⟩).symm⟩
  · rintro ⟨hz,hg⟩
    refine ⟨hz,?_⟩
    obtain ⟨u,hu⟩ := (heGraph (Z.decode ⟨z,hz⟩)).mpr hg
    exact ⟨u,hu.trans (nativeMixedPairCode_decode (n := n) (r := r) (m := m) (s := s) ⟨z,hz⟩)⟩

end DiamondIntegral.Section5
