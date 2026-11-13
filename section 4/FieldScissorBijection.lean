import «section 4».FieldDefinableRing
import «section 4».GaloisTaggedSum
import Section4.ResiduePureFunctions

/-! The actual definable bijection (A union B) + (A inter B) = A + B,
using the same explicit field tags as positive expressions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.FieldScissorBijection
open GaloisTaggedSum DefinableBiUniqueRelation
variable {K α : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem mem_cases (A B : Set (α → K)) (z : Option (α ⊕ α) → K)
    (hz : z ∈ taggedSum A B) :
    (∃ x ∈ A, z = leftTag x) ∨ (∃ y ∈ B, z = rightTag y) := by
  rcases hz with ⟨h0, hx, hR⟩ | ⟨h1, hy, hL⟩
  · refine Or.inl ⟨_, hx, ?_⟩
    funext i
    cases i with
    | none => exact h0
    | some i => cases i with
      | inl i => rfl
      | inr i => exact hR i
  · refine Or.inr ⟨_, hy, ?_⟩
    funext i
    cases i with
    | none => exact h1
    | some i => cases i with
      | inl i => exact hL i
      | inr i => rfl

theorem left_mem (A B : Set (α → K)) (x : α → K) (hx : x ∈ A) :
    leftTag x ∈ taggedSum A B := Or.inl ⟨rfl, hx, fun _ => rfl⟩

theorem right_mem (A B : Set (α → K)) (x : α → K) (hx : x ∈ B) :
    rightTag x ∈ taggedSum A B := Or.inr ⟨rfl, hx, fun _ => rfl⟩

abbrev Vars (α : Type) := Option (α ⊕ α) ⊕ Option (α ⊕ α)

def graph (A : Set (α → K)) : Set (Vars α → K) := {z |
  (z (.inl none) = 0 ∧ z (.inr none) = 0 ∧
    (fun i => z (.inl (some (.inl i)))) ∈ A ∧
    ∀ i, z (.inl (some (.inl i))) = z (.inr (some (.inl i)))) ∨
  (z (.inl none) = 0 ∧ z (.inr none) = 1 ∧
    (fun i => z (.inl (some (.inl i)))) ∉ A ∧
    ∀ i, z (.inl (some (.inl i))) = z (.inr (some (.inr i)))) ∨
  (z (.inl none) = 1 ∧ z (.inr none) = 1 ∧
    ∀ i, z (.inl (some (.inr i))) = z (.inr (some (.inr i))))}

theorem forall_eq {x y : α → K} : (∀ i, x i = y i) ↔ x = y := ⟨funext, fun h i => congrFun h i⟩

theorem graph_LL (A : Set (α → K)) (x y : α → K) :
    Sum.elim (leftTag x) (leftTag y) ∈ graph A ↔ x ∈ A ∧ x = y := by
  simp [graph, leftTag, forall_eq]

theorem graph_LR (A : Set (α → K)) (x y : α → K) :
    Sum.elim (leftTag x) (rightTag y) ∈ graph A ↔ x ∉ A ∧ x = y := by
  simp [graph, leftTag, rightTag, forall_eq]

theorem graph_RL (A : Set (α → K)) (x y : α → K) :
    Sum.elim (rightTag x) (leftTag y) ∉ graph A := by
  simp [graph, leftTag, rightTag]

theorem graph_RR (A : Set (α → K)) (x y : α → K) :
    Sum.elim (rightTag x) (rightTag y) ∈ graph A ↔ x = y := by
  simp [graph, rightTag, forall_eq]

theorem biunique (A B : Set (α → K)) :
    BiUnique (taggedSum (A ∪ B) (A ∩ B)) (taggedSum A B) (graph A) := by
  constructor
  · intro z hz
    rcases mem_cases _ _ z hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · by_cases ha : x ∈ A
      · refine ⟨leftTag x, ⟨left_mem A B x ha, (graph_LL A x x).mpr ⟨ha, rfl⟩⟩, ?_⟩
        rintro z ⟨hz, hr⟩
        rcases mem_cases _ _ z hz with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩
        · exact congrArg leftTag ((graph_LL A x y).mp hr).2.symm
        · exact (((graph_LR A x y).mp hr).1 ha).elim
      · have hb : x ∈ B := hx.resolve_left ha
        refine ⟨rightTag x, ⟨right_mem A B x hb, (graph_LR A x x).mpr ⟨ha, rfl⟩⟩, ?_⟩
        rintro z ⟨hz, hr⟩
        rcases mem_cases _ _ z hz with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩
        · exact (ha ((graph_LL A x y).mp hr).1).elim
        · exact congrArg rightTag ((graph_LR A x y).mp hr).2.symm
    · refine ⟨rightTag x, ⟨right_mem A B x hx.2, (graph_RR A x x).mpr rfl⟩, ?_⟩
      rintro z ⟨hz, hr⟩
      rcases mem_cases _ _ z hz with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩
      · exact (graph_RL A x y hr).elim
      · exact congrArg rightTag ((graph_RR A x y).mp hr).symm
  · intro z hz
    rcases mem_cases _ _ z hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · refine ⟨leftTag y, ⟨left_mem _ _ y (Or.inl hy), (graph_LL A y y).mpr ⟨hy, rfl⟩⟩, ?_⟩
      rintro z ⟨hz, hr⟩
      rcases mem_cases _ _ z hz with ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩
      · exact congrArg leftTag ((graph_LL A x y).mp hr).2
      · exact (graph_RL A x y hr).elim
    · by_cases ha : y ∈ A
      · refine ⟨rightTag y, ⟨right_mem _ _ y ⟨ha, hy⟩, (graph_RR A y y).mpr rfl⟩, ?_⟩
        rintro z ⟨hz, hr⟩
        rcases mem_cases _ _ z hz with ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩
        · obtain ⟨hx, he⟩ := (graph_LR A x y).mp hr
          exact (hx (he.symm ▸ ha)).elim
        · exact congrArg rightTag ((graph_RR A x y).mp hr)
      · refine ⟨leftTag y, ⟨left_mem _ _ y (Or.inr hy), (graph_LR A y y).mpr ⟨ha, rfl⟩⟩, ?_⟩
        rintro z ⟨hz, hr⟩
        rcases mem_cases _ _ z hz with ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩
        · exact congrArg leftTag ((graph_LR A x y).mp hr).2
        · have he := (graph_RR A x y).mp hr
          exact (ha (he ▸ hx.1)).elim

theorem graph_definable [Finite α] (A : Set (α → K)) (hA : PureDef A) : PureDef (graph A) := by
  have h00 : PureDef {z : Vars α → K | z (.inl none) = 0} := (pure_proj _).eq_const 0
  have h01 : PureDef {z : Vars α → K | z (.inl none) = 1} := (pure_proj _).eq_const 1
  have h10 : PureDef {z : Vars α → K | z (.inr none) = 0} := (pure_proj _).eq_const 0
  have h11 : PureDef {z : Vars α → K | z (.inr none) = 1} := (pure_proj _).eq_const 1
  have he (f g : α → Vars α) : PureDef {z : Vars α → K | ∀ i, z (f i) = z (g i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun _ => (pure_proj _).eq (pure_proj _))
  have ha := hA.preimage_comp (fun i => (Sum.inl (some (.inl i)) : Vars α))
  exact (h00.inter (h10.inter (ha.inter (he _ _)))).union
    ((h00.inter (h11.inter (ha.compl.inter (he _ _)))).union
      (h01.inter (h11.inter (he _ _))))

end DiamondIntegral.Section4.FieldScissorBijection
