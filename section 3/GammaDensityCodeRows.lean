import «section 3».GammaGroundRawGraphs
import «section 3».GammaGroundMeasuredVFData
import «section 3».RVUnitGammaFormGraph
import «section 5».NativeMixedCodeRealization
import IntegrationSection6.GammaWitnessVFCodesInBase

/-! Full invariant RV rows for an arbitrary Gamma-valued VF density.
The final RV slot ranges over every representative of the Gamma value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def gammaDensityCodeIndices (n r : ℕ) : ((Fin n ⊕ Fin r) ⊕ Fin 1) → Fin (n+(r+1))
  | .inl (.inl i) => Fin.castAdd (r+1) i
  | .inl (.inr i) => Fin.natAdd n (Fin.castAdd 1 i)
  | .inr i => Fin.natAdd n (Fin.natAdd r i)

def gammaDensityCodeRows {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    (ω : GammaGroundVolumeForm hc B A) : Set (Fin (n+(r+1)) → M) :=
  {w | w ∘ gammaDensityCodeIndices n r ∈ (rawMixedSpace n r).relation (volumeGammaSpace hc) ω.graph}

theorem gammaDensityCodeRows_proper
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    (ω : GammaGroundVolumeForm hc B A) (w) (hw : w ∈ gammaDensityCodeRows ω) :
    ∀ i, sortEval (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin (r+1) => .rv) i) (w i) := by
  obtain ⟨hs,hg,_⟩ := hw
  have hsorted (i : Fin n ⊕ Fin r) :
      sortEval (Coordinates.mixedSort i) ((w ∘ gammaDensityCodeIndices n r) (.inl i)) := by
    let q := (rawMixedSpace n r).decode ⟨_,hs⟩
    have hq := mixedValues_decode (n := n) (r := r) ⟨_,hs⟩
    have hh : sortEval (Coordinates.mixedSort i) (mixedValues q i) := by
      cases i with
      | inl i => exact (q.1 i).property
      | inr i => exact (q.2 i).property
    exact Eq.mp (congrArg (sortEval (Coordinates.mixedSort i)) (congrFun hq i)) hh
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left,gammaDensityCodeIndices,Function.comp_apply,Coordinates.mixedSort,Sum.elim_inl,Sum.elim_inr] using hsorted (.inl j)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_right,gammaDensityCodeIndices,Function.comp_apply,Coordinates.mixedSort,Sum.elim_inl,Sum.elim_inr] using hsorted (.inr j)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa only [Fin.append_right,sortEval,iRV,Function.comp_apply,gammaDensityCodeIndices] using hg.1

theorem gammaDensityCodeRows_definable
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    (ω : GammaGroundVolumeForm hc B A) :
    DefinableOverBase B (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin (r+1) => .rv))
      (gammaDensityCodeRows ω) :=
  (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B)
    (gammaDensityCodeRows_proper ω)).mp (ω.raw_graph_definable.preimage_comp (gammaDensityCodeIndices n r))

theorem gammaDensityCodeRows_mem
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    (ω : GammaGroundVolumeForm hc B A) (x : Section2.Mixed M n r)
    (c : (volumeGammaSpace hc).domain) :
    Fin.append (vfValues x.1) (Fin.append (rvValues x.2) c.val) ∈ gammaDensityCodeRows ω ↔
      ∃ a : A, a.val = x ∧ (ω a).val = (volumeGammaSpace hc).decode c := by
  let z : (rawMixedSpace (M := M) n r).domain := ⟨mixedValues x,mixedValues_mem_domain x⟩
  have he : (Fin.append (vfValues x.1) (Fin.append (rvValues x.2) c.val)) ∘ gammaDensityCodeIndices n r =
      Sum.elim z.val c.val := by
    funext i
    cases i with
    | inl i => cases i <;> simp only [gammaDensityCodeIndices,Function.comp_apply,Fin.append_left,
        Fin.append_right,Sum.elim_inl,Sum.elim_inr,z,mixedValues]
    | inr i => simp only [gammaDensityCodeIndices,Function.comp_apply,Fin.append_right,Sum.elim_inr]
  change ((Fin.append (vfValues x.1) (Fin.append (rvValues x.2) c.val)) ∘ gammaDensityCodeIndices n r ∈
    (rawMixedSpace n r).relation (volumeGammaSpace hc) ω.graph) ↔ _
  rw [he,(rawMixedSpace n r).relation_decode (volumeGammaSpace hc),decode_mixedValues]
  rfl

end DiamondIntegral.Section3
