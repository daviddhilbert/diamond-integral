import «section 2».RadiusProjection
import «section 2».FibreBadDefinability

/-! Lemma 2.54 over a fixed definable unary base, allowing empty fibres.
The exceptional set is the original-base definable projection of the
actual relative bad locus, and its finiteness is proved. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_2_54_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A})))
    (hopen : ∀ a ∈ I, IsOpen {x | (a,x) ∈ A}) :
    ∃ E ⊆ I, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      IsOpen {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ A} := by
  let C (a : Fin 1 → VF M) : Set (Fin n → VF M) :=
    {x | (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A}
  have hC : S.Definable LRV (vfCorrespondenceGraph I C) := relativeBadLocus_graph_definable hv I hI A hAI hA
  let E := {a ∈ I | (C a).Nonempty}
  have hE : S.Definable LRV (vfValues '' E) := by
    convert vfCorrespondence_hits_definable I C hC Set.univ (vf_univ_definable S) using 1
    ext z
    simp only [E,Set.Nonempty,Set.mem_univ,and_true]
  have hUnion := goodRadiusProjection_union_finite h00 hc hκ hs hv I A C hA hC (fun _ _ _ hx => hx)
  have hEf : E.Finite := hUnion.subset (by
    rintro a ⟨ha,x,hx⟩
    obtain ⟨γ,hγ⟩ := exists_vfBall_subset_nhds hv x ((hopen a ha).mem_nhds hx.1)
    exact Set.mem_iUnion.mpr ⟨γ,ha,x,hx,fun y hy => hγ hy⟩)
  refine ⟨E,fun _ h => h.1,hEf,hE,?_⟩
  apply open_restriction_of_bad_projection_subset I E A hAI
  rintro a ⟨p,hp,rfl⟩
  exact ⟨(hAI hp.1).1,p.2,hp⟩

theorem lemma_2_54_closed
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A})))
    (hclosed : ∀ a ∈ I, IsClosed {x | (a,x) ∈ A}) :
    ∃ E ⊆ I, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      IsClosed {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ A} := by
  let B := (I ×ˢ (Set.univ : Set (Fin n → VF M))) \ A
  have hBI : B ⊆ I ×ˢ Set.univ := Set.sdiff_subset
  have hB : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ B})) := by
    rw [vfPair_graph_eq I B hBI]
    have hAp : S.Definable LRV (vfPairValues '' A) := by rwa [vfPair_graph_eq I A hAI] at hA
    exact vfPair_sdiff_definable _ A (vfPair_base_definable I hI) hAp
  have hBopen : ∀ a ∈ I, IsOpen {x | (a,x) ∈ B} := by
    intro a ha
    have he : {x | (a,x) ∈ B} = {x | (a,x) ∈ A}ᶜ := by
      ext x
      exact and_iff_right ⟨ha,Set.mem_univ _⟩
    rw [he]
    exact (hclosed a ha).isOpen_compl
  obtain ⟨E,hEI,hEf,hE,hBop⟩ := lemma_2_54_open h00 hc hκ hs hv I hI B hBI hB hBopen
  refine ⟨E,hEI,hEf,hE,?_⟩
  have he : {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ A} =
      {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ B}ᶜ := by
    ext p
    change _ ↔ ¬ (_ ∧ _)
    rw [and_iff_right ⟨p.1.property.1,Set.mem_univ _⟩,not_not]
    rfl
  rw [he]
  exact hBop.isClosed_compl

/-- Lemma 2.54 in its fixed-base form. A true flag is the closed case,
a false flag the open case. The same-base finite exception is constructed. -/
theorem lemma_2_54
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (I : Set (Fin 1 → VF M)) (hI : S.Definable LRV (vfValues '' I))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M))) (hAI : A ⊆ I ×ˢ Set.univ)
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {x | (a,x) ∈ A})))
    (closed : Bool) (hfibres : ∀ a ∈ I,
      if closed then IsClosed {x | (a,x) ∈ A} else IsOpen {x | (a,x) ∈ A}) :
    ∃ E ⊆ I, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      if closed then IsClosed {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ A}
      else IsOpen {p : ↥(I \ E) × (Fin n → VF M) | (p.1.val,p.2) ∈ A} := by
  cases closed with
  | false => exact lemma_2_54_open h00 hc hκ hs hv I hI A hAI hA hfibres
  | true => exact lemma_2_54_closed h00 hc hκ hs hv I hI A hAI hA hfibres

end DiamondIntegral.Section2
