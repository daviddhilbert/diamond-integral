import «section 6».RegularizationParameterTransitions
import «section 6».FocusComponentImageTemplates
import «section 6».ParameterRelationComposition
import «section 6».RVPullbackParameterSemantics

/-! Finite templates for complete component sequences. Every
intermediate domain and protected image is computed by the actual
first-order transition relation. Whole-sequence admissibility and the
terminal preparation condition are definable over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s t k : ℕ}

structure MixedTransitionParameterTemplate (S : Set M) (p n r s : ℕ) where
  graph : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M)
  definable : S.Definable LRV graph

def MixedTransitionParameterTemplate.image (R : MixedTransitionParameterTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) : MixedSetParameterTemplate (M := M) S p n s :=
  mixedRelationImageTemplate A R.graph R.definable

inductive CentripetalProgramTemplate (S : Set M) (p n : ℕ) : ℕ → ℕ → Type where
  | identity (r : ℕ) : CentripetalProgramTemplate S p n r r
  | regularize (r : ℕ) : CentripetalProgramTemplate S p n r (n+r)
  | centripetal {r : ℕ} (T : FocusComponentParameterTemplate (M := M) S p n r) :
      CentripetalProgramTemplate S p n r (1+r)
  | comp {r s t : ℕ} (F : CentripetalProgramTemplate S p n r s) (H : CentripetalProgramTemplate S p n s t) :
      CentripetalProgramTemplate S p n r t

namespace CentripetalProgramTemplate

def transition : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    MixedSetParameterTemplate (M := M) S p n r → MixedTransitionParameterTemplate (M := M) S p n r s
  | _,_,.identity _,A => ⟨identityParameterTransition A,identityParameterTransition_definable A⟩
  | _,_,.regularize _,A => ⟨regularizationParameterTransition A,regularizationParameterTransition_definable A⟩
  | _,_,.centripetal T,A => ⟨focusComponentTransition T A,focusComponentTransition_definable T A⟩
  | _,_,.comp F H,A =>
      let R := F.transition A
      let Q := H.transition (R.image A)
      ⟨parameterRelationComp R.graph Q.graph,parameterRelationComp_definable _ _ R.definable Q.definable⟩

def target (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) := (T.transition A).image A

def pieceTarget (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A C : MixedSetParameterTemplate (M := M) S p n r) := (T.transition A).image C

def good : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    (A : MixedSetParameterTemplate (M := M) S p n r) →
    (Fin k → MixedSetParameterTemplate (M := M) S p n r) → Set (Fin p → M)
  | _,_,.identity _,_,_ => Set.univ
  | _,_,.regularize _,_,_ => Set.univ
  | _,_,.centripetal T,A,P => T.good A P
  | _,_,.comp F H,A,P => F.good A P ∩ H.good (F.target A) (fun i => F.pieceTarget A (P i))

theorem good_definable (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV (T.good A P) := by
  induction T with
  | identity r => exact Set.definable_univ
  | regularize r => exact Set.definable_univ
  | centripetal T => exact T.good_definable A P
  | comp F H ihF ihH => exact (ihF A P).inter (ihH (F.target A) (fun i => F.pieceTarget A (P i)))

def preparedGood (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : Set (Fin p → M) :=
  T.good A P ∩ ⋂ i,rvPullbackParameterLocus (T.pieceTarget A (P i)).typedGraph

theorem preparedGood_definable (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV (T.preparedGood A P) :=
  (T.good_definable A P).inter (Set.definable_iInter_of_finite (fun i =>
    rvPullbackParameterLocus_definable _ (T.pieceTarget A (P i)).typedGraph_definable))

end CentripetalProgramTemplate
end DiamondIntegral.Section6
