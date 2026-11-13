import «section 4».DefinableGaloisPoints
import Mathlib.ModelTheory.Definability

/-! A biunique definable relation supplies a definable partial bijection
and equal rational-point counts over a Galois base. This avoids requiring
a chosen function to be part of a specialization diagram. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.DefinableBiUniqueRelation
variable {K α β : Type*} [Field K]

structure BiUnique (S : Set (α → K)) (T : Set (β → K)) (R : Set ((α ⊕ β) → K)) : Prop where
  left : ∀ x ∈ S, ∃! y, y ∈ T ∧ Sum.elim x y ∈ R
  right : ∀ y ∈ T, ∃! x, x ∈ S ∧ Sum.elim x y ∈ R

variable {S : Set (α → K)} {T : Set (β → K)} {R : Set ((α ⊕ β) → K)}

def map (h : BiUnique S T R) (x : α → K) : β → K :=
  if hx : x ∈ S then Classical.choose (h.left x hx).exists else fun _ => 0

theorem map_spec (h : BiUnique S T R) {x : α → K} (hx : x ∈ S) :
    map h x ∈ T ∧ Sum.elim x (map h x) ∈ R := by
  unfold map
  rw [dif_pos hx]
  exact Classical.choose_spec (h.left x hx).exists

theorem bijOn (h : BiUnique S T R) : Set.BijOn (map h) S T := by
  refine ⟨fun _ hx => (map_spec h hx).1, ?_, ?_⟩
  · intro x hx y hy he
    exact (h.right (map h x) (map_spec h hx).1).unique
      ⟨hx, (map_spec h hx).2⟩ ⟨hy, by rw [he]; exact (map_spec h hy).2⟩
  · intro y hy
    obtain ⟨x, hx, _⟩ := h.right y hy
    exact ⟨x, hx.1, (h.left x hx.1).unique (map_spec h hx.1) ⟨hy, hx.2⟩⟩

theorem graph_eq (h : BiUnique S T R) :
    DefinableGaloisPoints.graphOn S (map h) =
      {w | w ∘ Sum.inl ∈ S ∧ w ∘ Sum.inr ∈ T ∧ w ∈ R} := by
  ext w
  constructor
  · rintro ⟨hx, he⟩
    have hm := map_spec h hx
    rw [he] at hm
    have hw : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
      funext i
      cases i <;> rfl
    exact ⟨hx, hm.1, hw ▸ hm.2⟩
  · rintro ⟨hx, hy, hR⟩
    refine ⟨hx, (h.left _ hx).unique (map_spec h hx) ⟨hy, ?_⟩⟩
    have hw : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
      funext i
      cases i <;> rfl
    exact hw.symm ▸ hR

theorem graph_definable [FirstOrder.Ring.CompatibleRing K] (h : BiUnique S T R)
    {A : Set K} (hS : A.Definable Language.ring S) (hT : A.Definable Language.ring T)
    (hR : A.Definable Language.ring R) :
    A.Definable Language.ring (DefinableGaloisPoints.graphOn S (map h)) := by
  rw [graph_eq]
  exact (hS.preimage_comp Sum.inl).inter ((hT.preimage_comp Sum.inr).inter hR)

theorem rational_count_eq {E : Type*} [Field E] [Algebra E K] [IsGalois E K]
    [FirstOrder.Ring.CompatibleRing K] (h : BiUnique S T R)
    (hS : (Set.range (algebraMap E K)).Definable Language.ring S)
    (hT : (Set.range (algebraMap E K)).Definable Language.ring T)
    (hR : (Set.range (algebraMap E K)).Definable Language.ring R) :
    (DefinableGaloisPoints.rationalPoints (E := E) S).ncard =
      (DefinableGaloisPoints.rationalPoints (E := E) T).ncard :=
  DefinableGaloisPoints.rational_count_eq (graph_definable h hS hT hR) (bijOn h)

end DiamondIntegral.Section4.DefinableBiUniqueRelation
