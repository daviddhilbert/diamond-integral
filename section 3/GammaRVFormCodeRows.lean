import «section 3».GammaGroundRawGraphs
import «section 3».RVUnitGammaFormGraph
import «section 3».GammaDensityCodeRows

/-! Every genuine Gamma form on an RV domain has a complete definable
RV code relation. The relation is functional only after the existing
Gamma quotient; all representatives of its value occur. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)}

def gammaRVFormCodeIndices (a : ℕ) : Fin a ⊕ Fin 1 → Fin (a+1) :=
  Sum.elim (Fin.castAdd 1) (Fin.natAdd a)

def gammaRVFormCodeRows (ω : GammaGroundVolumeForm hc B A) : Set (Fin (a+1) → M) :=
  {w | w ∘ gammaRVFormCodeIndices a ∈ (rawRVSpace a).relation (volumeGammaSpace hc) ω.graph}

theorem gammaRVFormCodeRows_proper (ω : GammaGroundVolumeForm hc B A)
    (w) (hw : w ∈ gammaRVFormCodeRows ω) :
    ∀ i, sortEval (SortTag.rv) (w i) := by
  obtain ⟨hx,hγ,_⟩ := hw
  let c : (rawRVSpace (M := M) a).domain := ⟨(w ∘ gammaRVFormCodeIndices a) ∘ Sum.inl,hx⟩
  have hs (j : Fin a) : iRV (w (Fin.castAdd 1 j)) := by
    have hp := ((rawRVSpace a).decode c j).property
    exact Eq.mp (congrArg iRV (congrFun (rvValues_decode c) j)) hp
  intro i
  refine Fin.addCases (fun j => hs j) (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hγ.1

theorem gammaRVFormCodeRows_definable (ω : GammaGroundVolumeForm hc B A) :
    DefinableOverBase B (fun _ : Fin (a+1) => .rv) (gammaRVFormCodeRows ω) :=
  (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) (gammaRVFormCodeRows_proper ω)).mp
    (ω.raw_graph_definable.preimage_comp (gammaRVFormCodeIndices a))

theorem gammaRVFormCodeRows_mem (ω : GammaGroundVolumeForm hc B A)
    (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    Fin.append (rvValues x) c.val ∈ gammaRVFormCodeRows ω ↔
      ∃ u : A, u.val = x ∧ (ω u).val = (volumeGammaSpace hc).decode c := by
  let d : (rawRVSpace (M := M) a).domain := ⟨rvValues x,⟨x,rfl⟩⟩
  have he : Fin.append (rvValues x) c.val ∘ gammaRVFormCodeIndices a = Sum.elim d.val c.val := by
    funext i
    cases i <;> simp only [gammaRVFormCodeIndices,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fin.append_left,Fin.append_right,d]
  change _ ∈ (rawRVSpace a).relation (volumeGammaSpace hc) ω.graph ↔ _
  rw [he,(rawRVSpace a).relation_decode (volumeGammaSpace hc)]
  have hd : (rawRVSpace a).decode d = x := rvValues_injective (rvValues_decode d)
  rw [hd]
  rfl

theorem gammaRVFormCodeRows_code (ω : GammaGroundVolumeForm hc B A)
    (w) (hw : w ∈ gammaRVFormCodeRows ω) : w ∘ Fin.natAdd a ∈ (volumeGammaSpace hc).domain :=
  hw.choose_spec.choose

end DiamondIntegral.Section3
