module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

public section

/-!
# Relative fibre closures in the fibrewise-continuity argument

The closure is taken in the tail space separately at each base point.
Relative closedness recovers the original family by intersection with its
domain. These are topological facts without a compactness or definability
premise; the definable finite-exception theorem is a separate step.
-/

set_option backward.isDefEq.respectTransparency false
open Set Topology

namespace DiamondIntegral.Section2
variable {I X Y : Type*} [TopologicalSpace X]

def fibreClosure (A : Set (I × X)) : Set (I × X) :=
  {p | p.2 ∈ closure {x | (p.1, x) ∈ A}}

theorem subset_fibreClosure (A : Set (I × X)) : A ⊆ fibreClosure A :=
  fun _ hp => subset_closure hp

theorem fibreClosure_fibres_isClosed (A : Set (I × X)) (a : I) :
    IsClosed {x : X | (a, x) ∈ fibreClosure A} := by
  change IsClosed (closure {x : X | (a, x) ∈ A})
  exact isClosed_closure

theorem fibreClosure_inter_of_relatively_closed
    (A B : Set (I × X)) (hAB : A ⊆ B)
    (hclosed : ∀ a : I, IsClosed {x : {x : X | (a, x) ∈ B} | (a, x.val) ∈ A}) :
    fibreClosure A ∩ B = A := by
  ext p
  constructor
  · rintro ⟨hp, hpB⟩
    let x : {x : X | (p.1, x) ∈ B} := ⟨p.2, hpB⟩
    have himage : Subtype.val '' {x : {x : X | (p.1, x) ∈ B} | (p.1, x.val) ∈ A} =
        {x : X | (p.1, x) ∈ A} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hAB hy⟩, hy, rfl⟩
    have hx : x ∈ closure {x : {x : X | (p.1, x) ∈ B} | (p.1, x.val) ∈ A} := by
      apply closure_subtype.mpr
      rw [himage]
      exact hp
    rw [(hclosed p.1).closure_eq] at hx
    exact hx
  · intro hp
    exact ⟨subset_fibreClosure A hp, hAB hp⟩

def fibreOpenExtension (A B : Set (I × X)) : Set (I × X) :=
  (fibreClosure (B \ A))ᶜ

theorem fibreOpenExtension_fibres_isOpen (A B : Set (I × X)) (a : I) :
    IsOpen {x : X | (a, x) ∈ fibreOpenExtension A B} :=
  (fibreClosure_fibres_isClosed (B \ A) a).isOpen_compl

theorem fibreOpenExtension_inter_of_relatively_open
    (A B : Set (I × X)) (hAB : A ⊆ B)
    (hopen : ∀ a : I, IsOpen {x : {x : X | (a, x) ∈ B} | (a, x.val) ∈ A}) :
    fibreOpenExtension A B ∩ B = A := by
  have hclosed (a : I) :
      IsClosed {x : {x : X | (a, x) ∈ B} | (a, x.val) ∈ B \ A} := by
    have he : {x : {x : X | (a, x) ∈ B} | (a, x.val) ∈ B \ A} =
        {x : {x : X | (a, x) ∈ B} | (a, x.val) ∈ A}ᶜ := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact (hopen a).isClosed_compl
  have he := fibreClosure_inter_of_relatively_closed (B \ A) B Set.sdiff_subset hclosed
  ext p
  constructor
  · rintro ⟨hp, hpB⟩
    by_contra hpA
    exact hp ((Set.ext_iff.mp he p).mpr ⟨hpB, hpA⟩).1
  · intro hpA
    refine ⟨?_, hAB hpA⟩
    intro hpcl
    exact ((Set.ext_iff.mp he p).mp ⟨hpcl, hAB hpA⟩).2 hpA

variable [TopologicalSpace Y]

def fibreGraph (A : Set (I × X)) (f : I → X → Y) : Set (I × (X × Y)) :=
  {p | (p.1, p.2.1) ∈ A ∧ p.2.2 = f p.1 p.2.1}

/-- A continuous fibre graph is recovered from its ambient closure by
intersecting with the original domain, as in Proposition 2.55. -/
theorem fibreClosure_graph_inter [T2Space Y]
    (A : Set (I × X)) (f : I → X → Y)
    (hf : ∀ a : I, Continuous (fun x : {x : X | (a, x) ∈ A} => f a x.val)) :
    fibreClosure (fibreGraph A f) ∩ {p : I × (X × Y) | (p.1, p.2.1) ∈ A} =
      fibreGraph A f := by
  apply fibreClosure_inter_of_relatively_closed
  · exact fun _ hp => hp.1
  · intro a
    let D := {z : X × Y | (a, z.1) ∈ A}
    let q : D → {x : X | (a, x) ∈ A} := fun z => ⟨z.val.1, z.property⟩
    have hq : Continuous q :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have h1 : Continuous (fun z : D => z.val.2) :=
      continuous_snd.comp continuous_subtype_val
    have h2 : Continuous (fun z : D => f a z.val.1) := (hf a).comp hq
    have he : {z : D | (a, z.val) ∈ fibreGraph A f} =
        {z : D | z.val.2 = f a z.val.1} := by
      ext z
      exact and_iff_right z.property
    change IsClosed {z : D | (a, z.val) ∈ fibreGraph A f}
    rw [he]
    exact isClosed_eq h1 h2

end DiamondIntegral.Section2
