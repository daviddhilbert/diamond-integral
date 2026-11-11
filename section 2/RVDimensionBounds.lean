import «section 2».RVMapProducts
import «section 2».RVProjectionDimension

/-! Dimension bounds for the finite unions and one-coordinate cylinders
in the approved RV-boundary induction. All maps keep the original base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rvDimension_lt_succ_iff_finite_map
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {m n : ℕ}
    (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    rvDimension S U < ((n+1 : ℕ) : WithBot ℕ) ↔ RVHasFiniteMap S U n := by
  classical
  constructor
  · intro hlt
    by_cases hne : U.Nonempty
    · let k := sInf {l | RVHasFiniteMap S U l}
      have hk : RVHasFiniteMap S U k := by
        change sInf {l | RVHasFiniteMap S U l} ∈ {l | RVHasFiniteMap S U l}
        exact Nat.sInf_mem ⟨m,rv_finite_map_to_arity hc S U hU⟩
      have hd : rvDimension S U = (k : WithBot ℕ) := by
        simp only [rvDimension,ite_eq_left hne,k]
      rw [hd] at hlt
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
      have hp := hk.append_constants hc (n-k)
      have he : k+(n-k) = n := by omega
      rwa [he] at hp
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact rv_finite_map_empty hc S
  · intro hmap
    exact lt_of_le_of_lt (rvDimension_le_of_finite_map hmap)
      (by exact_mod_cast Nat.lt_succ_self n)

theorem rvDimension_finite_union_lt
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {m n : ℕ}
    (Q : Set (Set (Fin m → RVInfinity M))) (hQ : Q.Finite)
    (hDefs : ∀ V ∈ Q, DefinableOver S (fun _ => .rv) (rvInputValues '' V))
    (hDims : ∀ V ∈ Q, rvDimension S V < ((n+1 : ℕ) : WithBot ℕ)) :
    rvDimension S (⋃₀ Q) < ((n+1 : ℕ) : WithBot ℕ) := by
  have hmaps : ∀ V ∈ Q, RVHasFiniteMap S V n := fun V hV =>
    (rvDimension_lt_succ_iff_finite_map hc S V (hDefs V hV)).mp (hDims V hV)
  exact lt_of_le_of_lt (rvDimension_le_of_finite_map
    (rv_finite_map_finite_union hc S Q hQ hmaps hDefs))
    (by exact_mod_cast Nat.lt_succ_self n)

theorem rvDimension_cylinder_lt
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {m n : ℕ}
    (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U))
    (hlt : rvDimension S U < (n : WithBot ℕ)) :
    rvDimension S (rvTupleProduct U (Set.univ : Set (Fin 1 → RVInfinity M))) <
      ((n+1 : ℕ) : WithBot ℕ) := by
  classical
  by_cases hne : U.Nonempty
  · let k := sInf {l | RVHasFiniteMap S U l}
    have hk : RVHasFiniteMap S U k := by
      change sInf {l | RVHasFiniteMap S U l} ∈ {l | RVHasFiniteMap S U l}
      exact Nat.sInf_mem ⟨m,rv_finite_map_to_arity hc S U hU⟩
    have hd : rvDimension S U = (k : WithBot ℕ) := by
      simp only [rvDimension,ite_eq_left hne,k]
    rw [hd] at hlt
    have hkn : k < n := by exact_mod_cast hlt
    have hunit := rv_finite_map_to_arity hc S (Set.univ : Set (Fin 1 → RVInfinity M))
      (rv_univ_definable S 1)
    exact lt_of_le_of_lt (rvDimension_le_of_finite_map (hk.product hc hunit))
      (by exact_mod_cast Nat.succ_lt_succ hkn)
  · have he : rvTupleProduct U (Set.univ : Set (Fin 1 → RVInfinity M)) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      ext x
      simp only [rvTupleProduct,Set.mem_ofPred_eq,Set.mem_empty_iff_false,false_and]
    rw [he,rvDimension_empty]
    simp

end DiamondIntegral.Section2
