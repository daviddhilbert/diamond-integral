import «section 4».GaloisPointCounts
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-! Disjoint union of field sets encoded with tags 0 and 1. The rational
point count is additive over every finite base field, in every arity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.GaloisTaggedSum
open DefinableGaloisPoints GaloisPointCounts
variable {E K α β : Type*} [Field E] [Field K] [Algebra E K]

def taggedSum (S : Set (α → K)) (T : Set (β → K)) : Set (Option (α ⊕ β) → K) :=
  {x | (x none = 0 ∧ (fun i => x (some (.inl i))) ∈ S ∧ ∀ j, x (some (.inr j)) = 0) ∨
    (x none = 1 ∧ (fun j => x (some (.inr j))) ∈ T ∧ ∀ i, x (some (.inl i)) = 0)}

def leftTag (x : α → K) : Option (α ⊕ β) → K
  | none => 0
  | some (.inl i) => x i
  | some (.inr _) => 0

def rightTag (y : β → K) : Option (α ⊕ β) → K
  | none => 1
  | some (.inl _) => 0
  | some (.inr j) => y j

def rationalEquiv (S : Set (α → K)) (T : Set (β → K)) :
    rationalPoints (E := E) (taggedSum S T) ≃
      (rationalPoints (E := E) S ⊕ rationalPoints (E := E) T) where
  toFun x :=
    if h0 : x.val none = 0 then
      have hL := x.property.1.resolve_right (fun h => zero_ne_one (h0.symm.trans h.1))
      .inl ⟨fun i => x.val (some (.inl i)), hL.2.1, fun i => x.property.2 (some (.inl i))⟩
    else
      have hR := x.property.1.resolve_left (fun h => h0 h.1)
      .inr ⟨fun j => x.val (some (.inr j)), hR.2.1, fun j => x.property.2 (some (.inr j))⟩
  invFun
    | .inl x => ⟨leftTag x.val, Or.inl ⟨rfl, x.property.1, fun _ => rfl⟩, fun i => by
        cases i with
        | none => exact ⟨0, map_zero _⟩
        | some i => cases i with
          | inl j => exact x.property.2 j
          | inr j => exact ⟨0, map_zero _⟩⟩
    | .inr y => ⟨rightTag y.val, Or.inr ⟨rfl, y.property.1, fun _ => rfl⟩, fun i => by
        cases i with
        | none => exact ⟨1, map_one _⟩
        | some i => cases i with
          | inl j => exact ⟨0, map_zero _⟩
          | inr j => exact y.property.2 j⟩
  left_inv x := by
    by_cases h0 : x.val none = 0
    · simp only [dif_pos h0]
      apply Subtype.ext
      funext i
      have hL := x.property.1.resolve_right (fun h => zero_ne_one (h0.symm.trans h.1))
      cases i with
      | none => exact h0.symm
      | some i => cases i with
        | inl j => rfl
        | inr j => exact (hL.2.2 j).symm
    · simp only [dif_neg h0]
      apply Subtype.ext
      funext i
      have hR := x.property.1.resolve_left (fun h => h0 h.1)
      cases i with
      | none => exact hR.1.symm
      | some i => cases i with
        | inl j => exact (hR.2.2 j).symm
        | inr j => rfl
  right_inv x := by
    cases x with
    | inl x =>
      simp [leftTag]
    | inr y =>
      simp [rightTag]

theorem count_add [Finite E] [Finite α] [Finite β] (S : Set (α → K)) (T : Set (β → K)) :
    count (E := E) (taggedSum S T) = count (E := E) S + count (E := E) T := by
  letI := FirstOrder.Ring.compatibleRingOfRing K
  letI : Finite (rationalPoints (E := E) S) := rationalPoints_finite S
  letI : Finite (rationalPoints (E := E) T) := rationalPoints_finite T
  change Nat.card (rationalPoints (E := E) (taggedSum S T)) = _
  rw [Nat.card_congr (rationalEquiv (E := E) S T), Nat.card_sum]
  rfl

end DiamondIntegral.Section4.GaloisTaggedSum
