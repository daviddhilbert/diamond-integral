import «section 6».VFScalarNameTemplates
import Section4.FunctionalRelations

/-! Scalar coefficient templates give actual original-base maps on
admissible VF parameter domains. The full graph is retained before any
RV-indexed scalar values or aperture radii are formed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

def vfScalarTemplateRelation (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S) (a : Fin p → VF M) (y : Fin 1 → VF M) : Prop :=
  a ∈ A.carrier ∧ Sum.elim (vfValues a) (Sum.elim Fin.elim0 (vfValues y)) ∈ T.graph

def vfScalarTemplateGraphIndex : Fin p ⊕ (Fin 0 ⊕ Fin 1) → Fin p ⊕ Fin 1 :=
  Sum.elim Sum.inl (Sum.elim Fin.elim0 Sum.inr)

theorem vfScalarTemplateRelation_definable (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S) :
    (rawVFSpace (M := M) p).RelationDefinable (rawVFSpace (M := M) 1) S (vfScalarTemplateRelation T A) := by
  let P := rawVFSpace (M := M) p
  let Q := rawVFSpace (M := M) 1
  have hSource := A.definable.preimage_comp (Sum.inl : Fin p → Fin p ⊕ Fin 1)
  have hTarget := (Q.definable_domain S).preimage_comp (Sum.inr : Fin 1 → Fin p ⊕ Fin 1)
  have hGraph := T.definable.preimage_comp vfScalarTemplateGraphIndex
  change S.Definable LRV (P.relation Q (vfScalarTemplateRelation T A))
  convert (hSource.inter hTarget).inter hGraph using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨hx,hy,hA,hT⟩
    refine ⟨⟨⟨hx,hA⟩,hy⟩,?_⟩
    have hX := vfValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    have hY := vfValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    have he : Sum.elim (vfValues (P.decode ⟨z ∘ Sum.inl,hx⟩))
        (Sum.elim Fin.elim0 (vfValues (Q.decode ⟨z ∘ Sum.inr,hy⟩)))=z ∘ vfScalarTemplateGraphIndex := by
      funext i
      rcases i with i | (i | i)
      · exact congrFun hX i
      · exact i.elim0
      · exact congrFun hY i
    change z ∘ vfScalarTemplateGraphIndex ∈ T.graph
    exact he ▸ hT
  · rintro ⟨⟨⟨hx,hA⟩,hy⟩,hT⟩
    refine ⟨hx,hy,hA,?_⟩
    have hX := vfValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    have hY := vfValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    have he : Sum.elim (vfValues (P.decode ⟨z ∘ Sum.inl,hx⟩))
        (Sum.elim Fin.elim0 (vfValues (Q.decode ⟨z ∘ Sum.inr,hy⟩)))=z ∘ vfScalarTemplateGraphIndex := by
      funext i
      rcases i with i | (i | i)
      · exact congrFun hX i
      · exact i.elim0
      · exact congrFun hY i
    exact he.symm ▸ hT

theorem vfScalarTemplateRelation_total (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S)
    (hGood : ∀ a : A,vfValues a.val ∈ T.good) (a : A) :
    ∃ y,vfScalarTemplateRelation T A a.val y := by
  refine ⟨T.value _ (hGood a) Fin.elim0,a.property,?_⟩
  have h0 : vfValues (Fin.elim0 : Fin 0 → VF M)=(Fin.elim0 : Fin 0 → M) := funext (fun i => i.elim0)
  simpa only [h0] using T.value_mem _ (hGood a) Fin.elim0

theorem vfScalarTemplateRelation_unique (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S)
    (hGood : ∀ a : A,vfValues a.val ∈ T.good) (a : Fin p → VF M) (y z : Fin 1 → VF M)
    (hy : vfScalarTemplateRelation T A a y) (hz : vfScalarTemplateRelation T A a z) : y=z :=
  vfValues_injective ((hGood ⟨a,hy.1⟩).1.2 Fin.elim0 (vfValues y) (vfValues z) hy.2 hz.2)

def vfScalarTemplateMap (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S) (hGood : ∀ a : A,vfValues a.val ∈ T.good) :
    Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  Map.ofFunctionalRelation (vfScalarTemplateRelation_definable T A)
    (fun _ _ h => ⟨h.1,Set.mem_univ _⟩) (vfScalarTemplateRelation_total T A hGood)
    (vfScalarTemplateRelation_unique T A hGood)

theorem vfScalarTemplateMap_relation (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S) (hGood : ∀ a : A,vfValues a.val ∈ T.good) (a : A) :
    vfScalarTemplateRelation T A a.val (vfScalarTemplateMap T A hGood a).val := by
  unfold vfScalarTemplateMap
  exact Map.ofFunctionalRelation_graph _ _ _ _ _

theorem vfScalarTemplateMap_value (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (A : DefSet (rawVFSpace (M := M) p) S) (hGood : ∀ a : A,vfValues a.val ∈ T.good) (a : A) :
    (vfScalarTemplateMap T A hGood a).val=T.value _ (hGood a) Fin.elim0 := by
  apply vfScalarTemplateRelation_unique T A hGood a.val
  · exact vfScalarTemplateMap_relation T A hGood a
  · refine ⟨a.property,?_⟩
    have h0 : vfValues (Fin.elim0 : Fin 0 → VF M)=(Fin.elim0 : Fin 0 → M) := funext (fun i => i.elim0)
    simpa only [h0] using T.value_mem _ (hGood a) Fin.elim0

end DiamondIntegral.Section6
