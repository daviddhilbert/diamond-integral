import «section 6».ProgramTransitionSorts
import «section 6».ProgramRVDataTraces

/-! Literal template identities for sequential composition. These
retain complete transition graphs, intermediate protected sets and RV
data traces when a finite program is reassociated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {p n r s t v k : ℕ}

theorem parameterRelationImage_comp {ι τ σ υ : Type} [Finite ι] [Finite τ] [Finite σ] [Finite υ]
    (A : Set (ι ⊕ τ → M)) (F : Set (ι ⊕ (τ ⊕ σ) → M)) (H : Set (ι ⊕ (σ ⊕ υ) → M)) :
    parameterRelationImage A (parameterRelationComp F H)=
      parameterRelationImage (parameterRelationImage A F) H := by
  ext z
  constructor
  · rintro ⟨x,⟨y,hF,hH⟩,hA⟩
    exact ⟨y,hH,x,hF,hA⟩
  · rintro ⟨y,hH,x,hF,hA⟩
    exact ⟨x,⟨y,hF,hH⟩,hA⟩

theorem parameterRelationComp_assoc {ι τ σ υ ν : Type}
    [Finite ι] [Finite τ] [Finite σ] [Finite υ] [Finite ν]
    (F : Set (ι ⊕ (τ ⊕ σ) → M)) (H : Set (ι ⊕ (σ ⊕ υ) → M))
    (K : Set (ι ⊕ (υ ⊕ ν) → M)) :
    parameterRelationComp (parameterRelationComp F H) K=
      parameterRelationComp F (parameterRelationComp H K) := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hF,hH⟩,hK⟩
    exact ⟨x,hF,y,hH,hK⟩
  · rintro ⟨x,hF,y,hH,hK⟩
    exact ⟨y,⟨x,hF,hH⟩,hK⟩

theorem MixedSetParameterTemplate.eq_of_graph_eq
    (A B : MixedSetParameterTemplate (M := M) S p n r) (h : A.graph=B.graph) : A=B := by
  cases A
  cases B
  cases h
  rfl

namespace CentripetalProgramTemplate

theorem pieceTarget_comp (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A C : MixedSetParameterTemplate (M := M) S p n r) :
    (F.comp H).pieceTarget A C=H.pieceTarget (F.target A) (F.pieceTarget A C) := by
  apply MixedSetParameterTemplate.eq_of_graph_eq
  change parameterRelationImage C.typedGraph (parameterRelationComp (F.transition A).graph
    (H.transition (F.target A)).graph)=
      parameterRelationImage (F.pieceTarget A C).typedGraph (H.transition (F.target A)).graph
  rw [F.image_typedGraph,parameterRelationImage_comp]
  rfl

theorem target_comp (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    (F.comp H).target A=H.target (F.target A) := pieceTarget_comp F H A A

theorem transition_comp_assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (K : CentripetalProgramTemplate (M := M) S p n t v)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    ((F.comp H).comp K).transition A=(F.comp (H.comp K)).transition A := by
  change MixedTransitionParameterTemplate.mk _ _=MixedTransitionParameterTemplate.mk _ _
  congr 1
  change parameterRelationComp (parameterRelationComp (F.transition A).graph (H.transition (F.target A)).graph)
    (K.transition ((F.comp H).target A)).graph=_
  rw [target_comp,parameterRelationComp_assoc]
  rfl

theorem good_comp_assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (K : CentripetalProgramTemplate (M := M) S p n t v)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    ((F.comp H).comp K).good A P=(F.comp (H.comp K)).good A P := by
  change (F.good A P ∩ H.good (F.target A) (fun i => F.pieceTarget A (P i))) ∩
    K.good ((F.comp H).target A) (fun i => (F.comp H).pieceTarget A (P i))=_
  simp only [target_comp,pieceTarget_comp,good,Set.inter_assoc]

theorem rvTrace_comp_assoc (F : CentripetalProgramTemplate (M := M) S p n r s)
    (H : CentripetalProgramTemplate (M := M) S p n s t)
    (K : CentripetalProgramTemplate (M := M) S p n t v)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    ((F.comp H).comp K).rvTrace A P=(F.comp (H.comp K)).rvTrace A P := by
  simp only [rvTrace,target_comp,pieceTarget_comp,List.append_assoc]

end CentripetalProgramTemplate
end DiamondIntegral.Section6
