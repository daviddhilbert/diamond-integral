import «section 6».UnaryRootSeparation
import «section 6».PureRVDiscQuotients

/-! Once centers are distinguished by their existing RV labels, their
actual VF coordinates descend to a full original-base definable map.
This gives genuine unary focus data on the surrounding tagged source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable (E : DefSet (rawMixedSpace (M := M) 1 r) S)
variable (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)

def unaryLabelCenterMap : Map (pureRVTagDomain E) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  definableSurjectiveDescent (pureRVTagQuotient E) (pureRVTagQuotient_surjective E) (mixedVFHeadMap E)
    (fun p q he => congrArg (mixedVFHeadMap E) (hUnique p q ((pureRVTagQuotient_eq_iff E p q).mp he)))

theorem unaryLabelCenterMap_at (p : E) :
    (unaryLabelCenterMap E hUnique (pureRVTagQuotient E p)).val=p.val.1 :=
  congrArg Subtype.val (definableSurjectiveDescent_apply _ _ _ _ p)

def unaryLabelCenter (u : Fin r → RVInfinity M) : VF M :=
  if hu : u ∈ (pureRVTagDomain E).carrier then (unaryLabelCenterMap E hUnique ⟨u,hu⟩).val 0 else 0

theorem unaryLabelCenter_at (p : E) : unaryLabelCenter E hUnique p.val.2=p.val.1 0 := by
  have hu : p.val.2 ∈ (pureRVTagDomain E).carrier := (pureRVTagQuotient E p).property
  rw [unaryLabelCenter,dif_pos hu]
  exact congrFun (unaryLabelCenterMap_at E hUnique p) 0

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryCenterActiveLabelMap : Map (focusActive A (pureRVTagDomain E)) (pureRVTagDomain E) where
  toFun p := ⟨p.val.2,p.property.2⟩
  graph_definable := (rvTailMap (focusActive A (pureRVTagDomain E))).graph_definable

def unaryLabelCenterFocusData (hEA : E.carrier ⊆ A.carrier)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    UnaryFocusData A where
  activeTags := pureRVTagDomain E
  focus := unaryLabelCenter E hUnique
  focusMap := (unaryLabelCenterMap E hUnique).comp (unaryCenterActiveLabelMap E)
  focusMap_eq p := by
    change (unaryLabelCenterMap E hUnique ⟨p.val.2,p.property.2⟩).val 0=unaryLabelCenter E hUnique p.val.2
    rw [unaryLabelCenter,dif_pos p.property.2]
  sourceProper := hA
  sourceDoublyBounded := hD
  tagged := hTag
  focusRV p hp hu := by
    obtain ⟨q,hq⟩ := (pureRVTagQuotient_surjective E) ⟨p.2,hu⟩
    have hqp : q.val.2=p.2 := congrArg Subtype.val hq
    rw [← hqp,unaryLabelCenter_at E hUnique q]
    exact congrFun (hTag q.val (hEA q.property) p hp hqp) 0

end DiamondIntegral.Section6
