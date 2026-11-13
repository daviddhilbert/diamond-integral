import «section 4».GammaFiniteGraphPartition
import «section 4».GammaPartialCellDefinability

/-! Finite partial Gamma graph partitions have total definable endpoint
extensions. On each active domain the endpoint retains its exact value;
active endpoint labels are unique and cover the original relation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaGraphPartitionEndpoints
open GammaOrderLogic GammaDefinableMaps GammaCellSections GammaPartialCellDefinability GammaFiniteGraphPartition
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ} {A : Set (Fin (n + 1) → Values.Gamma (M := M))}

theorem graph_definable (P : FiniteGraphPartition B A) (i : Fin P.size) :
    GammaDefinable B (graphCell (P.domain i) (P.function i)) := by
  have h := P.graph_definable i
  convert h using 1
  ext z
  exact and_congr_right (fun _ => eq_comm)

def endpoint (P : FiniteGraphPartition B A) (i : Fin P.size) :
    (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
  extend (P.domain i) (P.domain_definable i) (P.function i) (graph_definable P i)

theorem endpoint_definable (P : FiniteGraphPartition B A) (i : Fin P.size) : MapDefinable B (endpoint P i) :=
  extend_definable (P.domain i) (P.domain_definable i) (P.function i) (graph_definable P i)

theorem endpoint_on (P : FiniteGraphPartition B A) (i : Fin P.size)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ P.domain i) : endpoint P i y = P.function i y :=
  extend_on (P.domain i) (P.domain_definable i) (P.function i) (graph_definable P i) y hy

theorem endpoint_mem (P : FiniteGraphPartition B A) (i : Fin P.size)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ P.domain i) : Fin.cons (endpoint P i y) y ∈ A :=
  (P.covers _).mpr ⟨i, hy, (endpoint_on P i y hy).symm⟩

theorem endpoint_injective (P : FiniteGraphPartition B A) (y : Fin n → Values.Gamma (M := M))
    (i j : Fin P.size) (hi : y ∈ P.domain i) (hj : y ∈ P.domain j)
    (he : endpoint P i y = endpoint P j y) : i = j := by
  by_contra hij
  have hzi : Fin.cons (endpoint P i y) y ∈
      {z : Fin (n + 1) → Values.Gamma (M := M) |
        (fun l => z l.succ) ∈ P.domain i ∧ P.function i (fun l => z l.succ) = z 0} :=
    ⟨hi, (endpoint_on P i y hi).symm⟩
  have hzj : Fin.cons (endpoint P i y) y ∈
      {z : Fin (n + 1) → Values.Gamma (M := M) |
        (fun l => z l.succ) ∈ P.domain j ∧ P.function j (fun l => z l.succ) = z 0} :=
    ⟨hj, (endpoint_on P j y hj).symm.trans he.symm⟩
  exact Set.disjoint_left.mp (P.disjoint hij) hzi hzj

theorem exists_endpoint (P : FiniteGraphPartition B A) (y : Fin n → Values.Gamma (M := M))
    (x : Values.Gamma (M := M)) (hx : Fin.cons x y ∈ A) :
    ∃ i : Fin P.size, y ∈ P.domain i ∧ endpoint P i y = x := by
  obtain ⟨i, hi, he⟩ := (P.covers (Fin.cons x y)).mp hx
  exact ⟨i, hi, (endpoint_on P i y hi).trans he⟩

end DiamondIntegral.Section4.GammaGraphPartitionEndpoints
