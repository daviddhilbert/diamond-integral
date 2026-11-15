import IntegrationSection5.HeadPreparationExtension
import IntegrationSection5.UnarySpecialRelative
import IntegrationSection5.OrderedContractionProgram

/-! An actual unary special preparation completes an actual first head
stage. Carrier identifications reconcile their internal real presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S R : Set M} {m l : ℕ}

def headCompletionTail {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V) :
    SpecialBijection (T.extendBase hSR).contractedSet V :=
  specialCastBoth Q (PresentedSet.eq_of_carrier_eq
    (hU.trans (T.extendBase_contractedSet hSR).symm)) rfl

def headCompletionPreparation {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V)
    (hV : IsRVPullback (carrier V)) : HeadPreparation (T.extendBase hSR).contractedSet where
  arity := l
  target := V
  map := (headCompletionTail T hSR hU Q).toMap
  special := unary_specialRelative _
  saturated := headSaturated_of_pullback hV

def headUnaryCompletion {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V)
    (hV : IsRVPullback (carrier V)) :
    OrderedContractionProgram R (extendBase A hSR) (headImage V) :=
  .step (T.extendBase hSR) (.step (headCompletionPreparation T hSR hU Q hV) (.zero (headImage V)))

theorem headUnaryCompletion_volumeIndex {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V)
    (hV : IsRVPullback (carrier V)) :
    (headUnaryCompletion T hSR hU Q hV).volumeIndex =
      ![⟨1+(suffixIndex (special_chain_rvArity_le Q.chain) 0).val,by
          have h := (suffixIndex (special_chain_rvArity_le Q.chain) 0).isLt
          omega⟩,0] := by
  funext i
  fin_cases i
  · apply Fin.ext
    change (1+l)-(1+T.arity)+0 = 1+(l-(1+T.arity)+0)
    have hle := special_chain_rvArity_le Q.chain
    omega
  · apply Fin.ext
    change (1+l)-(1+l)+0 = 0
    omega

end IntegrationInACVF.Section5
