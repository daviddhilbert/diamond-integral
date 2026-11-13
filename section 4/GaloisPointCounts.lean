import «section 4».DefinableGaloisPoints
import Mathlib.Data.Set.Card

/-! Rational-point counts obey the scissor, product, point and affine-line
identities. For a finite base field these provide finite characteristic
characters once a finite collection of formulas has been specialized. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.GaloisPointCounts
open DefinableGaloisPoints
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {E K α β : Type*} [Field E] [Field K] [Algebra E K]

def count (S : Set (α → K)) : ℕ := (rationalPoints (E := E) S).ncard

theorem rational_empty : rationalPoints (E := E) (∅ : Set (α → K)) = ∅ := by
  ext x
  simp [rationalPoints]

theorem rational_union (S T : Set (α → K)) :
    rationalPoints (E := E) (S ∪ T) = rationalPoints (E := E) S ∪ rationalPoints (E := E) T := by
  ext x
  simp only [rationalPoints, Set.mem_setOf_eq, Set.mem_union]
  tauto

theorem rational_inter (S T : Set (α → K)) :
    rationalPoints (E := E) (S ∩ T) = rationalPoints (E := E) S ∩ rationalPoints (E := E) T := by
  ext x
  simp only [rationalPoints, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

theorem empty : count (E := E) (∅ : Set (α → K)) = 0 := by
  simp [count, rational_empty]

theorem scissor [Finite E] [Finite α] (S T : Set (α → K)) :
    count (E := E) (S ∪ T) + count (E := E) (S ∩ T) = count (E := E) S + count (E := E) T := by
  unfold count
  rw [rational_union, rational_inter]
  exact Set.ncard_union_add_ncard_inter _ _ (rationalPoints_finite S) (rationalPoints_finite T)

def rationalUnivEquiv : rationalPoints (E := E) (Set.univ : Set (α → K)) ≃ (α → E) where
  toFun x := fun i => Classical.choose (x.property.2 i)
  invFun x := ⟨algebraMap E K ∘ x, Set.mem_univ _, fun i => ⟨x i, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Classical.choose_spec (x.property.2 i)
  right_inv x := by
    funext i
    apply (algebraMap E K).injective
    exact Classical.choose_spec (show (algebraMap E K) (x i) ∈ Set.range (algebraMap E K) from ⟨x i, rfl⟩)

theorem univ [Finite E] [Finite α] :
    count (E := E) (Set.univ : Set (α → K)) = Nat.card E ^ Nat.card α := by
  change Nat.card (rationalPoints (E := E) (Set.univ : Set (α → K))) = _
  rw [Nat.card_congr (rationalUnivEquiv (E := E) (K := K) (α := α))]
  letI := Fintype.ofFinite E
  letI := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun]

theorem point [Finite E] : count (E := E) (Set.univ : Set (Fin 0 → K)) = 1 := by
  rw [univ]
  simp

theorem affine [Finite E] : count (E := E) (Set.univ : Set (Fin 1 → K)) = Nat.card E := by
  rw [univ]
  simp

def product (S : Set (α → K)) (T : Set (β → K)) : Set ((α ⊕ β) → K) :=
  {x | x ∘ Sum.inl ∈ S ∧ x ∘ Sum.inr ∈ T}

def rationalProductEquiv (S : Set (α → K)) (T : Set (β → K)) :
    rationalPoints (E := E) (product S T) ≃
      rationalPoints (E := E) S × rationalPoints (E := E) T where
  toFun x := (⟨x.val ∘ Sum.inl, x.property.1.1, fun i => x.property.2 (.inl i)⟩,
    ⟨x.val ∘ Sum.inr, x.property.1.2, fun i => x.property.2 (.inr i)⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val, ⟨x.1.property.1, x.2.property.1⟩,
    fun i => by cases i with
      | inl j => exact x.1.property.2 j
      | inr j => exact x.2.property.2 j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem mul (S : Set (α → K)) (T : Set (β → K)) :
    count (E := E) (product S T) = count (E := E) S * count (E := E) T := by
  change Nat.card (rationalPoints (E := E) (product S T)) = _
  rw [Nat.card_congr (rationalProductEquiv (E := E) S T), Nat.card_prod]
  rfl

end DiamondIntegral.Section4.GaloisPointCounts
