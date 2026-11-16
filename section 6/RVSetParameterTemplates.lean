import «section 6».MixedSetParameterTemplates

/-! Original-base parameter templates for the old-label active loci.
They combine with the current mixed-domain templates before a focus
graph is reconstructed or checked. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

structure RVSetParameterTemplate (S : Set M) (p r : ℕ) where
  graph : Set (Fin p ⊕ Fin r → M)
  definable : S.Definable LRV graph

def RVSetParameterTemplate.fibre (T : RVSetParameterTemplate (M := M) S p r) (a : Fin p → M) :
    DefSet (rawRVSpace (M := M) r) (S ∪ Set.range a) := by
  let P := rawRVSpace (M := M) r
  let fix (z : Fin r → M) := Sum.elim a z
  have hFix : (S ∪ Set.range a).DefinableMap LRV fix := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have hRow := (T.definable.mono Set.subset_union_left).preimage_map hFix
  refine ⟨{u | Sum.elim a (rvValues u) ∈ T.graph},?_⟩
  change (S ∪ Set.range a).Definable LRV (P.preimage _)
  convert (P.definable_domain _).inter hRow using 1
  ext z
  constructor
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (rvValues (P.decode ⟨z,hz⟩)) ∈ T.graph at hzT
    rw [SpecialTransformations.Section4.rvValues_decode] at hzT
    exact hzT
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (rvValues (P.decode ⟨z,hz⟩)) ∈ T.graph
    rw [SpecialTransformations.Section4.rvValues_decode]
    exact hzT

theorem exists_promoted_rv_set_template (a : Fin p → M)
    (A : DefSet (rawRVSpace (M := M) r) (S ∪ Set.range a)) :
    ∃ T : RVSetParameterTemplate (M := M) S p r,T.fibre a=A ∧
      {z : Fin r → M | Sum.elim a z ∈ T.graph}=(rawRVSpace r).preimage A.carrier := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a
    ((rawRVSpace r).preimage A.carrier) A.definable
  let H : Set (Fin p ⊕ Fin r → M) := {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}
  let T : RVSetParameterTemplate (M := M) S p r := ⟨H,hR⟩
  have hT : {z : Fin r → M | Sum.elim a z ∈ T.graph}=(rawRVSpace r).preimage A.carrier := by
    ext z
    exact Set.ext_iff.mp hSection z
  refine ⟨T,defSet_eq_of_carrier_eq ?_,hT⟩
  ext u
  have h := (rawRVSpace (M := M) r).preimage_decode A.carrier ⟨rvValues u,Set.mem_range_self _⟩
  rw [SpecialTransformations.Section4.decode_rvValues] at h
  exact (Set.ext_iff.mp hT _).trans h

def focusActiveParameterTemplate (A : MixedSetParameterTemplate (M := M) S p n r)
    (U : RVSetParameterTemplate (M := M) S p r) : MixedSetParameterTemplate (M := M) S p n r := by
  let tagCode (z : Fin p ⊕ (Fin n ⊕ Fin r) → M) :=
    Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (.inr j)))
  have hCode : S.DefinableMap LRV tagCode := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  exact ⟨{z | z ∈ A.typedGraph ∧ tagCode z ∈ U.graph},A.typedGraph_definable.inter (U.definable.preimage_map hCode)⟩

theorem focusActiveParameterTemplate_fibre (A : MixedSetParameterTemplate (M := M) S p n r)
    (U : RVSetParameterTemplate (M := M) S p r) (a : Fin p → M) :
    (focusActiveParameterTemplate A U).fibre a=focusActive (A.fibre a) (U.fibre a) := by
  apply defSet_eq_of_carrier_eq
  ext x
  change ((mixedValues x ∈ (rawMixedSpace n r).domain ∧ Sum.elim a (mixedValues x) ∈ A.graph) ∧
    Sum.elim a (rvValues x.2) ∈ U.graph) ↔
      Sum.elim a (mixedValues x) ∈ A.graph ∧ Sum.elim a (rvValues x.2) ∈ U.graph
  exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨mixedValues_mem_domain _,h.1⟩,h.2⟩⟩

end DiamondIntegral.Section6
