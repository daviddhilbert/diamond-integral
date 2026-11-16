import «section 6».ParameterSubstitutionTemplates
import «section 6».CentripetalProgramTemplates

/-! Definable parameter substitution commutes with the entire finite
program: every transition, intermediate domain, protected image and
admissibility test is retained. It changes all remaining data together. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s t k : ℕ}

theorem MixedSetParameterTemplate.ext_graph {A B : MixedSetParameterTemplate (M := M) S p n r}
    (h : A.graph=B.graph) : A=B := by
  cases A
  cases B
  cases h
  rfl

theorem mixedRelationImageTemplate_substitute
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M)) (hR : S.Definable LRV R)
    (h : DefinableParameterSubstitution (M := M) S p q) :
    (mixedRelationImageTemplate A R hR).substitute h=
      mixedRelationImageTemplate (A.substitute h) (parameterSubstitution h R) (parameterSubstitution_definable h R hR) := by
  apply MixedSetParameterTemplate.ext_graph
  ext z
  rfl

theorem MixedTransitionParameterTemplate.image_substitute
    (R : MixedTransitionParameterTemplate (M := M) S p n r s)
    (R' : MixedTransitionParameterTemplate (M := M) S q n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (he : R'.graph=parameterSubstitution h R.graph)
    (A : MixedSetParameterTemplate (M := M) S p n r) : R'.image (A.substitute h)=(R.image A).substitute h := by
  apply MixedSetParameterTemplate.ext_graph
  change parameterRelationImage (A.substitute h).typedGraph R'.graph=
    ((mixedRelationImageTemplate A R.graph R.definable).substitute h).graph
  rw [he]
  exact congrArg MixedSetParameterTemplate.graph (mixedRelationImageTemplate_substitute A R.graph R.definable h).symm

theorem focusComponentTransition_substitute
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) :
    focusComponentTransition (T.substitute h) (A.substitute h)=parameterSubstitution h (focusComponentTransition T A) := by
  ext z
  rfl

def CentripetalProgramTemplate.substitute (h : DefinableParameterSubstitution (M := M) S p q) :
    {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s → CentripetalProgramTemplate (M := M) S q n r s
  | _,_,.identity r => .identity r
  | _,_,.regularize r => .regularize r
  | _,_,.centripetal T => .centripetal (T.substitute h)
  | _,_,.comp F H => .comp (F.substitute h) (H.substitute h)

theorem CentripetalProgramTemplate.substitute_transition
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    ((T.substitute h).transition (A.substitute h)).graph=parameterSubstitution h (T.transition A).graph := by
  induction T with
  | identity r => rfl
  | regularize r => rfl
  | centripetal T => exact focusComponentTransition_substitute T A h
  | comp F H ihF ihH =>
    have hTarget := MixedTransitionParameterTemplate.image_substitute (F.transition A)
      ((F.substitute h).transition (A.substitute h)) h (ihF A) A
    change (F.substitute h).target (A.substitute h)=(F.target A).substitute h at hTarget
    change parameterRelationComp ((F.substitute h).transition (A.substitute h)).graph
      ((H.substitute h).transition ((F.substitute h).target (A.substitute h))).graph=
        parameterSubstitution h (parameterRelationComp (F.transition A).graph (H.transition (F.target A)).graph)
    rw [hTarget,ihF A,ihH (F.target A)]
    rfl

theorem CentripetalProgramTemplate.substitute_target
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    (T.substitute h).target (A.substitute h)=(T.target A).substitute h :=
  MixedTransitionParameterTemplate.image_substitute (T.transition A)
    ((T.substitute h).transition (A.substitute h)) h (T.substitute_transition h A) A

theorem CentripetalProgramTemplate.substitute_pieceTarget
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A P : MixedSetParameterTemplate (M := M) S p n r) :
    (T.substitute h).pieceTarget (A.substitute h) (P.substitute h)=(T.pieceTarget A P).substitute h :=
  MixedTransitionParameterTemplate.image_substitute (T.transition A)
    ((T.substitute h).transition (A.substitute h)) h (T.substitute_transition h A) P

theorem CentripetalProgramTemplate.substitute_good
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (T.substitute h).good (A.substitute h) (fun i => (P i).substitute h)=h.value ⁻¹' T.good A P := by
  induction T with
  | identity r => rfl
  | regularize r => rfl
  | centripetal T => exact T.substitute_good h A P
  | comp F H ihF ihH =>
    change (F.substitute h).good (A.substitute h) (fun i => (P i).substitute h) ∩
      (H.substitute h).good ((F.substitute h).target (A.substitute h))
        (fun i => (F.substitute h).pieceTarget (A.substitute h) ((P i).substitute h))=_
    have hPieces : (fun i => (F.substitute h).pieceTarget (A.substitute h) ((P i).substitute h))=
        (fun i => (F.pieceTarget A (P i)).substitute h) := funext (fun i => F.substitute_pieceTarget h A (P i))
    rw [ihF A P,F.substitute_target h A,hPieces,ihH (F.target A) (fun i => F.pieceTarget A (P i))]
    rfl

theorem rvPullbackParameterLocus_substitute
    (h : DefinableParameterSubstitution (M := M) S p q)
    (R : Set (Fin p ⊕ (Fin n ⊕ Fin r) → M)) :
    rvPullbackParameterLocus (parameterSubstitution h R)=h.value ⁻¹' rvPullbackParameterLocus R := by
  ext a
  rfl

theorem CentripetalProgramTemplate.substitute_preparedGood
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (T.substitute h).preparedGood (A.substitute h) (fun i => (P i).substitute h)=h.value ⁻¹' T.preparedGood A P := by
  ext a
  change (a ∈ (T.substitute h).good (A.substitute h) (fun i => (P i).substitute h) ∧ _) ↔ _
  rw [T.substitute_good h A P]
  simp only [CentripetalProgramTemplate.preparedGood,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
    T.substitute_pieceTarget h]
  rfl

end DiamondIntegral.Section6
