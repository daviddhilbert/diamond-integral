import «section 4».GammaIntegerFamilies

/-! A finite definable cover of Gamma tuples has a definable disjoint
first-match refinement, in every finite arity and over the original base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteFirstMatch
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def first {X : Type*} {m : ℕ} (C : Fin m → Set X) (i : Fin m) : Set X :=
  {x | x ∈ C i ∧ ∀ j, j < i → x ∉ C j}

theorem definable {B : Base (M := M)} {n m : ℕ}
    (C : Fin m → Set (Fin n → Values.Gamma (M := M))) (hC : ∀ i, GammaDefinable B (C i))
    (i : Fin m) : GammaDefinable B (first C i) := by
  have hU := finite_iUnion_definable_base B (fun j : {j : Fin m // j < i} => C j.val)
    (fun j => hC j.val)
  have h := inter_definable_base B _ _ (hC i) (complement_definable_base B _ hU)
  convert h using 1
  ext x
  simp only [first, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  constructor
  · rintro ⟨hx, hj⟩
    exact ⟨hx, fun ⟨j, hji⟩ => hj j hji⟩
  · rintro ⟨hx, hj⟩
    exact ⟨hx, fun j hji => hj ⟨j, hji⟩⟩

theorem disjoint {X : Type*} {m : ℕ} (C : Fin m → Set X) (i j : Fin m) (hij : i ≠ j) :
    Disjoint (first C i) (first C j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact hy.2 i h hx.1
  · exact hx.2 j h hy.1

theorem cover {X : Type*} {m : ℕ} (C : Fin m → Set X) (x : X) :
    (∃ i, x ∈ C i) ↔ ∃ i, x ∈ first C i := by
  constructor
  · rintro ⟨i, hi⟩
    let s := Finset.univ.filter (fun i => x ∈ C i)
    have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
    intro j hji hxj
    exact (not_lt_of_ge (s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩))) hji
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.1⟩

end DiamondIntegral.Section4.GammaFiniteFirstMatch
