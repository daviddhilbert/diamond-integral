import «section 6».UnaryRootControlStep

/-! One original-base finite obstacle family controls any finite list
of unary predicates, uniformly in every old RV tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_unary_obstacles
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) :
    ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      ∀ i, UnaryObstacleControl (G := G) Q (C i).carrier := by
  induction k with
  | zero =>
      refine ⟨∅,?_,fun i => i.elim0⟩
      simp only [Finset.coe_empty,Set.image_empty]
      change S.Definable LRV (∅ : Set (Fin 1 → M))
      exact Set.definable_empty
  | succ k ih =>
      obtain ⟨Q,hQ,hO⟩ := exists_unary_obstacles hc hv (C 0)
      obtain ⟨R,hR,hP⟩ := ih (Fin.tail C)
      refine ⟨Q ∪ R,?_,?_⟩
      · have he : Subtype.val '' ((Q ∪ R : Finset (VF M)) : Set (VF M)) =
            Subtype.val '' (Q : Set (VF M)) ∪ Subtype.val '' (R : Set (VF M)) := by
          rw [Finset.coe_union,Set.image_union]
        rw [he]
        exact hQ.union hR
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro a ρ havoid x hx y hy u
          exact hO a ρ (fun z hz => havoid z (Finset.mem_union_left R hz)) x hx y hy u
        · intro a ρ havoid x hx y hy u
          exact hP j a ρ (fun z hz => havoid z (Finset.mem_union_right Q hz)) x hx y hy u

theorem exists_controlling_unary_rootFamily
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) :
    ∃ R : UnaryRootFamily A, ∀ i, UnaryRootControl (G := G) R (C i).carrier := by
  obtain ⟨Q,hQ,hO⟩ := exists_finite_unary_obstacles hc hv C
  exact ⟨UnaryRootFamily.fromObstacles A Q hQ,fun i => UnaryRootFamily.fromObstacles_control Q hQ _ (hO i)⟩

end DiamondIntegral.Section6
