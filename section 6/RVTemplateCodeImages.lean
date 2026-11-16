import «section 6».ParameterCodeImages
import «section 6».RVSetParameterTemplates

/-! Complete RV-row images under definable code maps, finite unions
and restrictions of the parameter domain. These operations preserve
full representatives and introduce no additional parameter names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p r s : ℕ}
namespace RVSetParameterTemplate

def typedGraph (T : RVSetParameterTemplate (M := M) S p r) : Set (Fin p ⊕ Fin r → M) :=
  {z | z ∘ Sum.inr ∈ (rawRVSpace (M := M) r).domain ∧ z ∈ T.graph}

theorem typedGraph_definable (T : RVSetParameterTemplate (M := M) S p r) : S.Definable LRV T.typedGraph :=
  (((rawRVSpace (M := M) r).definable_domain S).preimage_comp
    (Sum.inr : Fin r → Fin p ⊕ Fin r)).inter T.definable

def codeImage (T : RVSetParameterTemplate (M := M) S p r)
    (F : (Fin p ⊕ Fin r → M) → Fin s → M) (hF : S.DefinableMap LRV F) :
    RVSetParameterTemplate (M := M) S p s :=
  ⟨parameterCodeImage T.typedGraph F,parameterCodeImage_definable _ T.typedGraph_definable F hF⟩

theorem codeImage_fibre (T : RVSetParameterTemplate (M := M) S p r)
    (F : (Fin p ⊕ Fin r → M) → Fin s → M) (hF : S.DefinableMap LRV F)
    (f : (Fin p → M) → (Fin r → RVInfinity M) → Fin s → RVInfinity M)
    (hCode : ∀ a u,F (Sum.elim a (rvValues u))=rvValues (f a u)) (a : Fin p → M) :
    ((T.codeImage F hF).fibre a).carrier=f a '' (T.fibre a).carrier := by
  ext u
  change rvValues u ∈ {z | Sum.elim a z ∈ parameterCodeImage T.typedGraph F} ↔ _
  rw [parameterCodeImage_at]
  constructor
  · rintro ⟨z,⟨hzDom,hzT⟩,hOut⟩
    let x : Fin r → RVInfinity M := (rawRVSpace (M := M) r).decode ⟨z,hzDom⟩
    have hX : rvValues x=z := SpecialTransformations.Section4.rvValues_decode _
    have hxT : x ∈ (T.fibre a).carrier := by
      change Sum.elim a (rvValues x) ∈ T.graph
      rw [hX]
      exact hzT
    change F (Sum.elim a z)=rvValues u at hOut
    rw [← hX,hCode a x] at hOut
    exact ⟨x,hxT,rvValues_injective hOut⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨rvValues x,⟨⟨x,rfl⟩,hx⟩,hCode a x⟩

def restrictParameters (T : RVSetParameterTemplate (M := M) S p r)
    (X : Set (Fin p → M)) (hX : S.Definable LRV X) : RVSetParameterTemplate (M := M) S p r :=
  ⟨{z | z ∘ Sum.inl ∈ X ∧ z ∈ T.graph},(hX.preimage_comp Sum.inl).inter T.definable⟩

theorem restrictParameters_fibre (T : RVSetParameterTemplate (M := M) S p r)
    (X : Set (Fin p → M)) (hX : S.Definable LRV X) (a : Fin p → M) :
    ((T.restrictParameters X hX).fibre a).carrier={u | a ∈ X ∧ u ∈ (T.fibre a).carrier} := rfl

def finiteUnion {I : Type} [Finite I] (T : I → RVSetParameterTemplate (M := M) S p r) :
    RVSetParameterTemplate (M := M) S p r :=
  ⟨⋃ i,(T i).graph,Set.definable_iUnion_of_finite (fun i => (T i).definable)⟩

theorem finiteUnion_fibre {I : Type} [Finite I] (T : I → RVSetParameterTemplate (M := M) S p r) (a : Fin p → M) :
    ((finiteUnion T).fibre a).carrier=⋃ i,((T i).fibre a).carrier := by
  ext u
  simp only [finiteUnion,fibre,Set.mem_setOf_eq,Set.mem_iUnion]

end RVSetParameterTemplate
end DiamondIntegral.Section6
