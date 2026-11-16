import «section 6».ParameterSubstitutionTemplates

/-! The complete RV row of a unary VF parameter template is an actual
original-base definable relation on the mixed unary source and RV output. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m : ℕ}

def unaryRVRowRelation (V : RVSetParameterTemplate (M := M) S 1 m)
    (x : Mixed M 1 r) (u : Fin m → RVInfinity M) : Prop :=
  u ∈ (V.fibre (fun _ => (x.1 0).val)).carrier

def unaryRVRowRelationIndex : Fin 1 ⊕ Fin m → (Fin 1 ⊕ Fin r) ⊕ Fin m :=
  Sum.elim (fun _ => .inl (.inl 0)) Sum.inr

theorem unaryRVRowRelation_definable (V : RVSetParameterTemplate (M := M) S 1 m) :
    (rawMixedSpace 1 r).RelationDefinable (rawRVSpace m) S (unaryRVRowRelation V) := by
  let P := rawMixedSpace (M := M) 1 r
  let Q := rawRVSpace (M := M) m
  have hX := (P.definable_domain S).preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
  have hY := (Q.definable_domain S).preimage_comp (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
  have hV := V.definable.preimage_comp (unaryRVRowRelationIndex (r := r) (m := m))
  change S.Definable LRV (P.relation Q (unaryRVRowRelation V))
  convert (hX.inter hY).inter hV using 1
  ext z
  have hAt (hx : z ∘ Sum.inl ∈ P.domain) (hy : z ∘ Sum.inr ∈ Q.domain) :
      Sum.elim (fun _ : Fin 1 => ((P.decode ⟨z ∘ Sum.inl,hx⟩).1 0).val)
        (rvValues (Q.decode ⟨z ∘ Sum.inr,hy⟩))=z ∘ unaryRVRowRelationIndex := by
    have hCodeX := mixedValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    have hCodeY := SpecialTransformations.Section4.rvValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    funext i
    cases i with
    | inl i => exact congrFun hCodeX (.inl 0)
    | inr i => exact congrFun hCodeY i
  constructor
  · rintro ⟨hx,hy,hData⟩
    refine ⟨⟨hx,hy⟩,?_⟩
    change z ∘ unaryRVRowRelationIndex ∈ V.graph
    exact hAt hx hy ▸ hData
  · rintro ⟨⟨hx,hy⟩,hData⟩
    refine ⟨hx,hy,?_⟩
    change Sum.elim (fun _ : Fin 1 => ((P.decode ⟨z ∘ Sum.inl,hx⟩).1 0).val)
      (rvValues (Q.decode ⟨z ∘ Sum.inr,hy⟩)) ∈ V.graph
    change z ∘ unaryRVRowRelationIndex ∈ V.graph at hData
    exact (hAt hx hy).symm ▸ hData

end DiamondIntegral.Section6
