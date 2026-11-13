import «section 4».FieldDefinableRing
import «section 4».FiniteTupleBlocks
import Section4.ResiduePureFunctions

/-! Actual Cartesian charts and their multiplication formula in the
pure-field definable presentation, using the project's tuple convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.FieldCartesianCharts
open FieldDefinableRing FiniteTupleBlocks DefinableBiUniqueRelation
variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def product (a b : Chart K) : Chart K where
  arity := b.arity + a.arity
  domain := {z | z ∘ headIndex b.arity a.arity ∈ a.domain ∧
    z ∘ tailIndex b.arity a.arity ∈ b.domain}
  definable := (a.definable.preimage_comp (headIndex b.arity a.arity)).inter
    (b.definable.preimage_comp (tailIndex b.arity a.arity))

def graph (a b : Chart K) : Set ((Fin (b.arity + a.arity) ⊕ (Fin a.arity ⊕ Fin b.arity)) → K) :=
  {z | (∀ i, z (.inl (headIndex b.arity a.arity i)) = z (.inr (.inl i))) ∧
    (∀ j, z (.inl (tailIndex b.arity a.arity j)) = z (.inr (.inr j)))}

theorem graph_definable (a b : Chart K) : PureDef (graph a b) := by
  have ha (i : Fin a.arity) : PureDef {z : (Fin (b.arity + a.arity) ⊕ (Fin a.arity ⊕ Fin b.arity)) → K | z (.inl (headIndex b.arity a.arity i)) =
      z (.inr (.inl i))} := (pure_proj _).eq (pure_proj _)
  have hb (j : Fin b.arity) : PureDef {z : (Fin (b.arity + a.arity) ⊕ (Fin a.arity ⊕ Fin b.arity)) → K | z (.inl (tailIndex b.arity a.arity j)) =
      z (.inr (.inr j))} := (pure_proj _).eq (pure_proj _)
  have ha' := Set.definable_iInter_of_finite ha
  have hb' := Set.definable_iInter_of_finite hb
  convert ha'.inter hb' using 1
  ext z
  simp only [graph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]

theorem graph_biunique (a b : Chart K) :
    BiUnique (product a b).domain
      (FieldDefinableRing.domain K (.mul (.atom a) (.atom b))) (graph a b) := by
  constructor
  · intro x hx
    let y := Sum.elim (x ∘ headIndex b.arity a.arity) (x ∘ tailIndex b.arity a.arity)
    refine ⟨y, ⟨⟨hx.1, hx.2⟩, (fun _ => rfl), (fun _ => rfl)⟩, ?_⟩
    rintro y' ⟨_, hh, ht⟩
    funext i
    cases i with
    | inl i => exact (hh i).symm
    | inr i => exact (ht i).symm
  · intro y hy
    let x := join b.arity a.arity (y ∘ Sum.inl) (y ∘ Sum.inr)
    have hh : x ∘ headIndex b.arity a.arity = y ∘ Sum.inl := funext (join_head _ _ _ _)
    have ht : x ∘ tailIndex b.arity a.arity = y ∘ Sum.inr := funext (join_tail _ _ _ _)
    refine ⟨x, ⟨⟨hh.symm ▸ hy.1, ht.symm ▸ hy.2⟩,
      (fun i => congrFun hh i), (fun i => congrFun ht i)⟩, ?_⟩
    rintro x' ⟨_, hh', ht'⟩
    have hhead : x' ∘ headIndex b.arity a.arity = y ∘ Sum.inl := funext hh'
    have htail : x' ∘ tailIndex b.arity a.arity = y ∘ Sum.inr := funext ht'
    exact (join_reconstruct _ _ x').symm.trans
      (congrArg₂ (join b.arity a.arity) hhead htail)

theorem objectClass_product (a b : Chart K) :
    objectClass K (product a b) = objectClass K a * objectClass K b := by
  have h := FieldDefinableRing.relation_zero K (.atom (product a b))
    (.mul (.atom a) (.atom b)) (graph a b) (graph_definable a b) (graph_biunique a b)
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of (product a b)) =
    Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a * FreeCommRing.of b) at h
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of (product a b)) =
    Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a) *
      Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of b)
  rw [← map_mul]
  exact h

end DiamondIntegral.Section4.FieldCartesianCharts
