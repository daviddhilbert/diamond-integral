import «section 4».GammaSortedFibres
import «section 4».GammaFamilyBoundary

/-! A uniformly finite Gamma relation is partitioned into actual partial
function graphs, all over the original base. Applied to the intrinsic
boundary relation, this supplies canonical boundary functions for cells. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteGraphPartition
open GammaOrderLogic GammaSortedFibres GammaTupleCounting FiniteOrderRanks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rankGraph_cover {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite)
    (N : ℕ) (hb : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.ncard ≤ N)
    (z : Fin (n + 1) → Values.Gamma (M := M)) :
    z ∈ R ↔ ∃ i : Fin N, z ∈ RankGraph R i.val := by
  constructor
  · intro hz
    let y := fun j : Fin n => z j.succ
    have hez : Fin.cons (z 0) y = z := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hx : Fin.cons (z 0) y ∈ R := hez.symm ▸ hz
    let k := setRank {x | Fin.cons x y ∈ R} (z 0)
    have hk : k < N := (setRank_lt_ncard _ (hf y) (z 0) hx).trans_le (hb y)
    exact ⟨⟨k, hk⟩, hz, rfl⟩
  · rintro ⟨i, hi⟩
    exact hi.1

theorem rankGraph_disjoint {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (N : ℕ) :
    Pairwise (fun i j : Fin N => Disjoint (RankGraph R i.val) (RankGraph R j.val)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact hij (Fin.ext (hi.2.symm.trans hj.2))

structure FiniteGraphPartition (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) where
  size : ℕ
  domain : Fin size → Set (Fin n → Values.Gamma (M := M))
  function : Fin size → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)
  domain_definable : ∀ i, GammaDefinable B (domain i)
  graph_definable : ∀ i, GammaDefinable B
    {z : Fin (n + 1) → Values.Gamma (M := M) |
      (fun j => z j.succ) ∈ domain i ∧ function i (fun j => z j.succ) = z 0}
  covers : ∀ z, z ∈ R ↔ ∃ i : Fin size,
    (fun j => z j.succ) ∈ domain i ∧ function i (fun j => z j.succ) = z 0
  disjoint : Pairwise (fun i j : Fin size => Disjoint
    {z : Fin (n + 1) → Values.Gamma (M := M) |
      (fun j => z j.succ) ∈ domain i ∧ function i (fun j => z j.succ) = z 0}
    {z : Fin (n + 1) → Values.Gamma (M := M) |
      (fun l => z l.succ) ∈ domain j ∧ function j (fun l => z l.succ) = z 0})

def canonicalPartition (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite)
    (N : ℕ) (hb : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.ncard ≤ N) :
    FiniteGraphPartition B R where
  size := N
  domain i := {y | AtLeast R (i.val + 1) y}
  function i := pointMap R hf i.val
  domain_definable i := atLeast_definable_base B R hR (i.val + 1)
  graph_definable i := pointMap_graph_definable B R hR hf i.val
  covers z := by
    change z ∈ R ↔ ∃ i : Fin N, z ∈
      {z | AtLeast R (i.val + 1) (fun j => z j.succ) ∧ pointMap R hf i.val (fun j => z j.succ) = z 0}
    simp_rw [pointMap_graph_eq R hf]
    exact rankGraph_cover R hf N hb z
  disjoint := by
    intro i j hij
    change Disjoint
      {z : Fin (n + 1) → Values.Gamma (M := M) |
        AtLeast R (i.val + 1) (fun l => z l.succ) ∧ pointMap R hf i.val (fun l => z l.succ) = z 0}
      {z : Fin (n + 1) → Values.Gamma (M := M) |
        AtLeast R (j.val + 1) (fun l => z l.succ) ∧ pointMap R hf j.val (fun l => z l.succ) = z 0}
    rw [pointMap_graph_eq R hf, pointMap_graph_eq R hf]
    exact rankGraph_disjoint R N hij

theorem exists_boundaryPartition (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    Nonempty (FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) := by
  obtain ⟨N, hb⟩ := GammaFamilyBoundary.uniform_boundary_bound h00 hκ hs B hr hγ R hR
  exact ⟨canonicalPartition B (GammaFamilyBoundary.Boundary R)
    (GammaFamilyBoundary.boundary_definable_base B R hR) (fun y => (hb y).1) N (fun y => (hb y).2)⟩

end DiamondIntegral.Section4.GammaFiniteGraphPartition
