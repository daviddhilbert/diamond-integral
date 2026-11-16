import «section 6».PromotedContinuousRVTemplates

/-! Complete parameter templates for the actual mixed domains at
every stage of a finite transformation. Specialization has exactly the
original base and the given real parameter tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

structure MixedSetParameterTemplate (S : Set M) (p n r : ℕ) where
  graph : Set (Fin p ⊕ (Fin n ⊕ Fin r) → M)
  definable : S.Definable LRV graph

namespace MixedSetParameterTemplate
def typedGraph (T : MixedSetParameterTemplate (M := M) S p n r) : Set (Fin p ⊕ (Fin n ⊕ Fin r) → M) :=
  {z | z ∘ Sum.inr ∈ (rawMixedSpace (M := M) n r).domain ∧ z ∈ T.graph}

theorem typedGraph_definable (T : MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV T.typedGraph :=
  (((rawMixedSpace (M := M) n r).definable_domain S).preimage_comp
    (Sum.inr : Fin n ⊕ Fin r → Fin p ⊕ (Fin n ⊕ Fin r))).inter T.definable

def fibre (T : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) :
    DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a) := by
  let P := rawMixedSpace (M := M) n r
  let fix (z : Fin n ⊕ Fin r → M) := Sum.elim a z
  have hFix : (S ∪ Set.range a).DefinableMap LRV fix := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have hRow := (T.definable.mono Set.subset_union_left).preimage_map hFix
  refine ⟨{x | Sum.elim a (mixedValues x) ∈ T.graph},?_⟩
  change (S ∪ Set.range a).Definable LRV (P.preimage _)
  convert (P.definable_domain _).inter hRow using 1
  ext z
  constructor
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (mixedValues (P.decode ⟨z,hz⟩)) ∈ T.graph at hzT
    rw [mixedValues_decode] at hzT
    exact hzT
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (mixedValues (P.decode ⟨z,hz⟩)) ∈ T.graph
    rw [mixedValues_decode]
    exact hzT

theorem fibre_code (T : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) :
    (rawMixedSpace n r).preimage (T.fibre a).carrier=
      {z : Fin n ⊕ Fin r → M | Sum.elim a z ∈ T.typedGraph} := by
  ext z
  constructor
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (mixedValues ((rawMixedSpace n r).decode ⟨z,hz⟩)) ∈ T.graph at hzT
    rw [mixedValues_decode] at hzT
    exact hzT
  · rintro ⟨hz,hzT⟩
    refine ⟨hz,?_⟩
    change Sum.elim a (mixedValues ((rawMixedSpace n r).decode ⟨z,hz⟩)) ∈ T.graph
    rw [mixedValues_decode]
    exact hzT

end MixedSetParameterTemplate

theorem exists_promoted_mixed_set_template (a : Fin p → M)
    (A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)) :
    ∃ T : MixedSetParameterTemplate (M := M) S p n r,T.fibre a=A ∧
      {z : Fin n ⊕ Fin r → M | Sum.elim a z ∈ T.graph}=(rawMixedSpace n r).preimage A.carrier := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a
    ((rawMixedSpace n r).preimage A.carrier) A.definable
  let H : Set (Fin p ⊕ (Fin n ⊕ Fin r) → M) := {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}
  let T : MixedSetParameterTemplate (M := M) S p n r := ⟨H,hR⟩
  have hT : {z : Fin n ⊕ Fin r → M | Sum.elim a z ∈ T.graph}=(rawMixedSpace n r).preimage A.carrier := by
    ext z
    exact Set.ext_iff.mp hSection z
  refine ⟨T,defSet_eq_of_carrier_eq ?_,hT⟩
  ext x
  have h := (rawMixedSpace (M := M) n r).preimage_decode A.carrier
    ⟨mixedValues x,mixedValues_mem_domain _⟩
  rw [decode_mixedValues] at h
  exact (Set.ext_iff.mp hT _).trans h

end DiamondIntegral.Section6
