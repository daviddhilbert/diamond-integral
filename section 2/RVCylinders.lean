import «section 2».RVMapDomains
import Mathlib.Logic.Equiv.Fin.Basic

/-! A cylinder adds one RV coordinate in any specified position. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

def lastToCoordinate {n : ℕ} (i : Fin (n+1)) : Fin (n+1) ≃ Fin (n+1) :=
  (finSuccEquiv' (Fin.last n)).trans (finSuccEquiv' i).symm

theorem lastToCoordinate_castSucc {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    lastToCoordinate i j.castSucc = i.succAbove j := by
  simp only [lastToCoordinate,Equiv.trans_apply,finSuccEquiv'_last_apply_castSucc,
    finSuccEquiv'_symm_some]

theorem lastToCoordinate_last {n : ℕ} (i : Fin (n+1)) :
    lastToCoordinate i (Fin.last n) = i := by
  simp only [lastToCoordinate,Equiv.trans_apply,finSuccEquiv'_at,finSuccEquiv'_symm_none]

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvCoordinateCylinder {n : ℕ} (i : Fin (n+1)) (U : Set (Fin n → RVInfinity M)) :
    Set (Fin (n+1) → RVInfinity M) := {t | Fin.removeNth i t ∈ U}

theorem rvCoordinateCylinder_eq_reindexed {n : ℕ} (i : Fin (n+1))
    (U : Set (Fin n → RVInfinity M)) :
    rvCoordinateCylinder i U = rvReindexed (lastToCoordinate i).symm
      (rvTupleProduct U (Set.univ : Set (Fin 1 → RVInfinity M))) := by
  ext t
  have hex : (t ∘ lastToCoordinate i) ∘ Fin.castAdd 1 = Fin.removeNth i t := by
    funext j
    exact congrArg t (lastToCoordinate_castSucc i j)
  change Fin.removeNth i t ∈ U ↔
    ((t ∘ lastToCoordinate i) ∘ Fin.castAdd 1 ∈ U ∧
      (t ∘ lastToCoordinate i) ∘ Fin.natAdd n ∈ (Set.univ : Set (Fin 1 → RVInfinity M)))
  rw [hex]
  simp only [Set.mem_univ,and_true]

theorem rvCoordinateCylinder_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} (i : Fin (n+1)) (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' rvCoordinateCylinder i U) := by
  rw [rvCoordinateCylinder_eq_reindexed]
  have hp := (rv_finite_map_to_arity hc S U hU).product hc
    (rv_finite_map_to_arity hc S _ (rv_univ_definable S 1))
  exact (hp.reindex hc _).domain_definable

theorem rvDimension_coordinate_cylinder_lt (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n k : ℕ} (i : Fin (n+1)) (U : Set (Fin n → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U))
    (hlt : rvDimension S U < (k : WithBot ℕ)) :
    rvDimension S (rvCoordinateCylinder i U) < ((k+1 : ℕ) : WithBot ℕ) := by
  rw [rvCoordinateCylinder_eq_reindexed]
  have hp := (rv_finite_map_to_arity hc S U hU).product hc
    (rv_finite_map_to_arity hc S _ (rv_univ_definable S 1))
  exact lt_of_le_of_lt (rvDimension_reindex_le hc S _ _ hp.domain_definable)
    (rvDimension_cylinder_lt hc S U hU hlt)

end DiamondIntegral.Section2
