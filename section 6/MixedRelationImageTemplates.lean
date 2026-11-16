import «section 6».ParameterRelationImages

/-! Exact intermediate mixed-domain templates computed from complete
transition relations, including literal images of all protected pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem MixedSetParameterTemplate.fibre_eq_of_code_row
    (T : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (B : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a))
    (hRow : {z | Sum.elim a z ∈ T.graph}=(rawMixedSpace n r).preimage B.carrier) : T.fibre a=B := by
  apply defSet_eq_of_carrier_eq
  ext x
  have h := (rawMixedSpace (M := M) n r).preimage_decode B.carrier
    ⟨mixedValues x,mixedValues_mem_domain _⟩
  rw [decode_mixedValues] at h
  exact (Set.ext_iff.mp hRow _).trans h

def mixedRelationImageTemplate (C : MixedSetParameterTemplate (M := M) S p n r)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (hR : S.Definable LRV R) : MixedSetParameterTemplate (M := M) S p n s :=
  ⟨parameterRelationImage C.typedGraph R,parameterRelationImage_definable _ _ C.typedGraph_definable hR⟩

theorem mixedRelationImageTemplate_at_restriction (C : MixedSetParameterTemplate (M := M) S p n r)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (hR : S.Definable LRV R) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} (f : Map A B)
    (hCA : (C.fibre a).carrier ⊆ A.carrier)
    (hGraph : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph) :
    (mixedRelationImageTemplate C R hR).fibre a=(f.restrict hCA).image := by
  exact (mixedRelationImageTemplate C R hR).fibre_eq_of_code_row a (f.restrict hCA).image
    (parameterRelationImage_at_restriction (P := rawMixedSpace n r) (Q := rawMixedSpace n s) (S := S)
      a C.typedGraph R f hCA (C.fibre_code a).symm hGraph)

theorem mixedRelationImageTemplate_at_image (C : MixedSetParameterTemplate (M := M) S p n r)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (hR : S.Definable LRV R) (a : Fin p → M)
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} (f : Map (C.fibre a) B)
    (hGraph : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n s) f.graph) :
    (mixedRelationImageTemplate C R hR).fibre a=f.image := by
  exact mixedRelationImageTemplate_at_restriction C R hR a f (fun _ h => h) hGraph

end DiamondIntegral.Section6
