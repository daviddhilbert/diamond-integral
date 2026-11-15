import «section 5».InvariantAffineCover
import Mathlib.Data.Finset.Max

/-! The invariant affine cover yields a finite disjoint invariant
stratification. Each stratum is an actual closed subset of its displayed
affine open, with unique membership and no omitted residual locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical CategoryTheory AlgebraicGeometry

def orderedOpenPiece {T : Type*} [TopologicalSpace T] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens T) (i : Fin n) : Set T :=
  {z | z ∈ U i ∧ ∀ j, j < i → z ∉ U j}

theorem orderedOpenPiece_closed {T : Type*} [TopologicalSpace T] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens T) (i : Fin n) :
    IsClosed {z : U i | z.val ∈ orderedOpenPiece U i} := by
  have he : {z : U i | z.val ∈ orderedOpenPiece U i} =
      ⋂ j : Fin n, ⋂ (_ : j < i), {z : U i | z.val ∉ U j} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    change (z.val ∈ U i ∧ ∀ j, j < i → z.val ∉ U j) ↔ ∀ j, j < i → z.val ∉ U j
    exact ⟨And.right, fun h => ⟨z.property, h⟩⟩
  rw [he]
  exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    ((U j).isOpen.preimage continuous_subtype_val).isClosed_compl))

theorem orderedOpenPiece_unique {T : Type*} [TopologicalSpace T] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens T) (hc : ∀ z, ∃ i, z ∈ U i) (z : T) :
    ∃! i, z ∈ orderedOpenPiece U i := by
  let s := Finset.univ.filter (fun i : Fin n => z ∈ U i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hc z
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := s.min' hs
  have hi : i ∈ s := Finset.min'_mem s hs
  have hp : z ∈ orderedOpenPiece U i := by
    refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
    intro j hji hj
    have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    exact (not_lt_of_ge (Finset.min'_le s j hjmem)) hji
  refine ⟨i, hp, ?_⟩
  intro j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hji | hij
  · exact hp.2 j hji hj.1
  · exact hj.2 i hij hp.1

theorem orderedOpenPiece_invariant {T : Type*} [TopologicalSpace T] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens T) (f : T → T)
    (hU : ∀ i z, f z ∈ U i ↔ z ∈ U i) (i : Fin n) (z : T) :
    f z ∈ orderedOpenPiece U i ↔ z ∈ orderedOpenPiece U i :=
  and_congr (hU i z) (forall_congr' (fun j => imp_congr_right (fun _ => not_congr (hU j z))))

theorem finite_invariant_affine_stratification {X : Scheme} [X.IsSeparated] [CompactSpace X]
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut X)
    (hgood : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, schemePointAction ρ g x ∈ U) :
    ∃ n : ℕ, ∃ U : Fin n → X.Opens, ∃ S : Fin n → Set X,
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, IsClosed {z : U i | z.val ∈ S i}) ∧
      (∀ z, ∃! i, z ∈ S i) ∧
      (∀ i g z, schemePointAction ρ g z ∈ S i ↔ z ∈ S i) := by
  obtain ⟨s, V, hV, hInv, hc⟩ := finite_invariant_affine_cover ρ hgood
  let n := Fintype.card s
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  let U : Fin n → X.Opens := fun i => V (e i).val
  have hcover (z : X) : ∃ i, z ∈ U i := by
    obtain ⟨x, hx, hz⟩ := hc z
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change z ∈ V (e (e.symm ⟨x, hx⟩)).val
    rw [e.apply_symm_apply]
    exact hz
  refine ⟨n, U, (fun i => orderedOpenPiece U i), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hV (e i).val
  · intro i z h
    exact h.1
  · exact fun i => orderedOpenPiece_closed U i
  · exact fun z => orderedOpenPiece_unique U hcover z
  · intro i g z
    exact orderedOpenPiece_invariant U (schemePointAction ρ g) (fun j => hInv (e j).val g) i z

end DiamondIntegral.Section5
