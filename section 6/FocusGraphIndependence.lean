import «section 6».BinaryGraphParameterLoci

/-! The definable independence test characterizes actual partial
focus maps. Thus the coordinate-erasing condition can be included in
compactness before reconstructing a permitted component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

theorem mem_focusIndependentParameterLocus_map_iff
    (R : Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M)) (a : ι → M) (j : Fin n)
    {A : DefSet (rawMixedSpace (M := M) n r) T}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) T))
    (hSection : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph) :
    a ∈ focusIndependentParameterLocus R j ↔
      ∀ p q : A,p.val.2=q.val.2 → (∀ i ≠ j,p.val.1 i=q.val.1 i) →
        (f p).val 0=(f q).val 0 := by
  have hAt (z) : Sum.elim a z ∈ R ↔
      ∃ p : A,Sum.elim (mixedValues p.val) (vfValues (f p).val)=z :=
    (Set.ext_iff.mp hSection z).trans (scalarMapGraph_iff f z)
  constructor
  · intro h p q hRV hOther
    have hp := (hAt _).mpr ⟨p,rfl⟩
    have hq := (hAt _).mpr ⟨q,rfl⟩
    have hInd := h _ _ hp hq
    change (∀ k,(p.val.2 k).val=(q.val.2 k).val) →
      (∀ i,i ≠ j → (p.val.1 i).val=(q.val.1 i).val) →
        ((f p).val 0).val=((f q).val 0).val at hInd
    exact Subtype.ext (hInd (fun k => congrArg (fun u => (u k).val) hRV)
      (fun i hi => congrArg Subtype.val (hOther i hi)))
  · intro h x y hx hy
    obtain ⟨p,rfl⟩ := (hAt x).mp hx
    obtain ⟨q,rfl⟩ := (hAt y).mp hy
    change (∀ k,(p.val.2 k).val=(q.val.2 k).val) →
      (∀ i,i ≠ j → (p.val.1 i).val=(q.val.1 i).val) →
        ((f p).val 0).val=((f q).val 0).val
    intro hRV hOther
    exact congrArg Subtype.val (h p q (funext (fun k => Subtype.ext (hRV k)))
      (fun i hi => Subtype.ext (hOther i hi)))

end DiamondIntegral.Section6
