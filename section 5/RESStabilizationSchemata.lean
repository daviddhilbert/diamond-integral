import «section 5».RESStabilizationExpressions
import «section 5».RESExpressionBijections

/-! A full native equality schema retains the common stabilizer, every
oriented coefficient relation, and one literal total-domain bijection.
Its validity locus is original-base definable and its native equality is proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem original_list_predicate_validity_definable {ι : Type} (L : List ι)
    (P : ι → (Fin p → M) → Prop)
    (hP : ∀ i ∈ L, DefinableOverBase B sp {z | P i z}) :
    DefinableOverBase B sp {z | z ∈ sortedUniverse sp ∧ ∀ i ∈ L, P i z} := by
  have h : OriginalSortedPredicate B sp (fun z => ∀ i : Fin L.length, P (L.get i) z) :=
    OriginalSortedPredicate.finite_all (fun i =>
      OriginalSortedPredicate.of_definable (hP (L.get i) (List.get_mem _ _)))
  apply h.congr
  intro z _
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hi
    exact h j
  · exact fun h i => h _ (List.get_mem _ _)

structure RESStabilizationSchema (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) where
  stabilizer : List ((a : ℕ) × RESSetSchema B p a sp)
  terms : List (RESRelationTermSchema B p sp)
  graph : GammaRelationFormula B p
    (resStabilizedExpression F stabilizer (resRelationRightExpression terms)).1
    (resStabilizedExpression G stabilizer (resRelationLeftExpression terms)).1 sp

def RESStabilizationSchema.sourceExpression {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESStabilizationSchema F G) : (a : ℕ) × RESExpressionSchema B p sp a :=
  resStabilizedExpression F W.stabilizer (resRelationRightExpression W.terms)
def RESStabilizationSchema.targetExpression {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESStabilizationSchema F G) : (a : ℕ) × RESExpressionSchema B p sp a :=
  resStabilizedExpression G W.stabilizer (resRelationLeftExpression W.terms)

def RESStabilizationSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp} (W : RESStabilizationSchema F G)
    (z : Fin p → M) : Prop :=
  F.Valid hc z ∧ G.Valid hc z ∧
    (∀ C ∈ W.stabilizer, C.2.Valid hc z) ∧ (∀ T ∈ W.terms, T.Valid hc z) ∧
    bijectiveMapRowValid sp (fun _ : Fin W.targetExpression.1 => .rv)
      W.sourceExpression.2.setSchema.domain.val W.targetExpression.2.setSchema.domain.val W.graph.val z

theorem RESStabilizationSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp} (W : RESStabilizationSchema F G) :
    DefinableOverBase B sp {z | W.Valid hc z} := by
  have hC := original_list_predicate_validity_definable W.stabilizer
    (fun C z => C.2.Valid hc z) (fun C _ => C.2.valid_definable hc)
  have hT := original_list_predicate_validity_definable W.terms
    (fun T z => T.Valid hc z) (fun T _ => T.valid_definable hc)
  have hb := gamma_bijection_validity_definable sp
    (fun _ : Fin W.sourceExpression.1 => .rv) (fun _ : Fin W.targetExpression.1 => .rv)
    W.sourceExpression.2.setSchema.domain.property W.targetExpression.2.setSchema.domain.property W.graph.property
  have h := (F.valid_definable hc).inter ((G.valid_definable hc).inter (hC.inter (hT.inter hb)))
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ _)
  have hp : F.Valid hc z → z ∈ sortedUniverse sp := fun hz => hz.1
  constructor
  · rintro ⟨hf, hg, hc, ht, hb⟩
    exact ⟨hf, hg, ⟨hp hf, hc⟩, ⟨hp hf, ht⟩, hb⟩
  · rintro ⟨hf, hg, ⟨_, hc⟩, ⟨_, ht⟩, hb⟩
    exact ⟨hf, hg, hc, ht, hb⟩

theorem RESStabilizationSchema.sourceExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESStabilizationSchema F G) (z : Fin p → M) (h : W.Valid hc z) :
    W.sourceExpression.2.Valid hc z :=
  resStabilizedExpression_valid hc F W.stabilizer (resRelationRightExpression W.terms) z h.1 h.2.2.1
    (resRelationRightExpression_valid hc W.terms z h.1.1 h.2.2.2.1)

theorem RESStabilizationSchema.targetExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESStabilizationSchema F G) (z : Fin p → M) (h : W.Valid hc z) :
    W.targetExpression.2.Valid hc z :=
  resStabilizedExpression_valid hc G W.stabilizer (resRelationLeftExpression W.terms) z h.2.1 h.2.2.1
    (resRelationLeftExpression_valid hc W.terms z h.1.1 h.2.2.2.1)

theorem RESStabilizationSchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESStabilizationSchema F G) (z : Fin p → M) (h : W.Valid hc z) :
    nativeRESChartClass (F.chart hc z h.1) = nativeRESChartClass (G.chart hc z h.2.1) := by
  let H : RESExpressionBijectionSchema W.sourceExpression.2 W.targetExpression.2 := ⟨W.graph⟩
  have hH : H.Valid hc z := ⟨W.sourceExpression_valid hc z h, W.targetExpression_valid hc z h, h.2.2.2.2⟩
  have he := H.native_equality hc z hH
  let c := (resListExpression W.stabilizer).2.nativeValue hc z
    (resListExpression_valid hc W.stabilizer z h.1.1 h.2.2.1)
  let l := (resRelationLeftExpression W.terms).2.nativeValue hc z
    (resRelationLeftExpression_valid hc W.terms z h.1.1 h.2.2.2.1)
  let r := (resRelationRightExpression W.terms).2.nativeValue hc z
    (resRelationRightExpression_valid hc W.terms z h.1.1 h.2.2.2.1)
  have hr : l = r := resRelationExpressions_native_equality hc W.terms z h.1.1 h.2.2.2.1
  change nativeRESChartClass (F.chart hc z h.1) + (c+r) =
    nativeRESChartClass (G.chart hc z h.2.1) + (c+l) at he
  rw [hr] at he
  exact add_right_cancel he

end DiamondIntegral.Section5
