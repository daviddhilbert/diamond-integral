import «section 4».RVResidueChartCodes
import «section 4».RVResidueJoinedCovers
import «section 4».BiUniqueTransport

/-! Actual original-base RV bijective relations give equal pure-field
classes after decoding. This applies to codes of different tuple arities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueCodeRelations
open RVResidueChartCodes RVResidueScaledCovers FiniteTupleBlocks DefinableBiUniqueRelation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem map_join {X Y : Type*} (f : X → Y) (m n : ℕ) (x : Fin n → X) (y : Fin m → X) :
    (fun i => f (join m n x y i)) = join m n (f ∘ x) (f ∘ y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (Fin.tail x)) j) i

theorem restrict_relation {F α β : Type*} {D : Set (α → F)} {E : Set (β → F)}
    {R : Set ((α ⊕ β) → F)} (h : BiUnique D E R) :
    BiUnique D E {z | z ∘ Sum.inl ∈ D ∧ z ∘ Sum.inr ∈ E ∧ z ∈ R} := by
  constructor
  · intro x hx
    obtain ⟨y, ⟨hy, hr⟩, huniq⟩ := h.left x hx
    refine ⟨y, ⟨hy, hx, hy, hr⟩, ?_⟩
    rintro y' ⟨hy', _, _, hr'⟩
    exact huniq y' ⟨hy', hr'⟩
  · intro y hy
    obtain ⟨x, ⟨hx, hr⟩, huniq⟩ := h.right y hy
    refine ⟨x, ⟨hx, hx, hy, hr⟩, ?_⟩
    rintro x' ⟨hx', _, _, hr'⟩
    exact huniq x' ⟨hx', hr'⟩

def graph {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (R : Set (Fin (m + n) → M)) :
    Set ((Fin C.chart.arity ⊕ Fin D.chart.arity) → ModelResidue M) :=
  {z | z ∘ Sum.inl ∈ C.chart.domain ∧ z ∘ Sum.inr ∈ D.chart.domain ∧
    join m n (rvValues (C.decode (z ∘ Sum.inl))) (rvValues (D.decode (z ∘ Sum.inr))) ∈ R}

theorem graph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Base (M := M)} {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (R : Set (Fin (m + n) → M))
    (hR : DefinableOverBase P (fun _ : Fin (m + n) => .rv) R) :
    PureDef (graph C D R) := by
  have hdom := (C.chart.definable.preimage_comp Sum.inl).inter
    (D.chart.definable.preimage_comp Sum.inr)
  have h := RVResidueScaledCovers.pullback_definable hc hdom
    (RVResidueJoinedCovers.coverJoin C.cover D.cover) R hR
  convert h using 1
  ext z
  change (_ ∧ _ ∧ join m n _ _ ∈ R) ↔ ((_ ∧ _) ∧ rvValues (join m n _ _) ∈ R)
  have he := map_join (fun t : CanonicalRV.RVSort M => t.val) m n
    (C.decode (z ∘ Sum.inl)) (D.decode (z ∘ Sum.inr))
  change rvValues (join m n _ _) = join m n (rvValues _) (rvValues _) at he
  rw [he]
  tauto

theorem graph_biunique {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (R : Set (Fin (m + n) → M))
    (h : BiUnique A B {z | join m n (z ∘ Sum.inl) (z ∘ Sum.inr) ∈ R}) :
    BiUnique C.chart.domain D.chart.domain (graph C D R) := by
  have ht := restrict_relation (BiUniqueTransport.pullback
    (fun x => rvValues (C.decode x)) (fun y => rvValues (D.decode y)) C.bijective D.bijective _ h)
  simpa only [graph, Set.mem_setOf_eq, Sum.elim_comp_inl, Sum.elim_comp_inr] using ht

theorem objectClass_eq (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Base (M := M)} {n m : ℕ} {A : Set (Fin n → M)} {B : Set (Fin m → M)}
    (C : RawCode A) (D : RawCode B) (R : Set (Fin (m + n) → M))
    (hR : DefinableOverBase P (fun _ : Fin (m + n) => .rv) R)
    (h : BiUnique A B {z | join m n (z ∘ Sum.inl) (z ∘ Sum.inr) ∈ R}) :
    FieldDefinableRing.objectClass (ModelResidue M) C.chart =
      FieldDefinableRing.objectClass (ModelResidue M) D.chart :=
  FieldDefinableRing.relation_zero (ModelResidue M) (.atom C.chart) (.atom D.chart)
    (graph C D R) (graph_definable hc C D R hR) (graph_biunique C D R h)

end DiamondIntegral.Section4.RVResidueCodeRelations
