import «section 6».FocusComponentTransitionSemantics
import «section 6».MixedRelationImageTemplates

/-! A component's next ambient and protected families are computed
over the original base. Their specializations are exactly its actual
image and the literal images of its restrictions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

def FocusComponentParameterTemplate.imageTemplate (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) : MixedSetParameterTemplate (M := M) S p n (1+r) :=
  mixedRelationImageTemplate A (focusComponentTransition T A) (focusComponentTransition_definable T A)

def FocusComponentParameterTemplate.pieceImageTemplate (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A C : MixedSetParameterTemplate (M := M) S p n r) : MixedSetParameterTemplate (M := M) S p n (1+r) :=
  mixedRelationImageTemplate C (focusComponentTransition T A) (focusComponentTransition_definable T A)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FocusComponentParameterTemplate.imageTemplate_at (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hF : a ∈ T.focus.good) (hC : a ∈ T.coefficient.good)
    (D : CentripetalData (G := G) (A.fibre a)) (hj : D.coordinate=T.coordinate)
    (hU : D.activeTags=T.active.fibre a) (hCoeff : D.coefficient=vfScalarTemplateValue T.coefficient a hC)
    (hFocus : ∀ q : focusActive (A.fibre a) (T.active.fibre a),D.extendedFocus q.val=
      T.focus.value a hF q.val.2 q.val.1 0) : (T.imageTemplate A).fibre a=D.map.image :=
  mixedRelationImageTemplate_at_image A (focusComponentTransition T A) (focusComponentTransition_definable T A)
    a D.map (focusComponentTransition_at T A a hF hC D hj hU hCoeff hFocus)

theorem FocusComponentParameterTemplate.pieceImageTemplate_at (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A C : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hF : a ∈ T.focus.good) (hC : a ∈ T.coefficient.good)
    (D : CentripetalData (G := G) (A.fibre a)) (hj : D.coordinate=T.coordinate)
    (hU : D.activeTags=T.active.fibre a) (hCoeff : D.coefficient=vfScalarTemplateValue T.coefficient a hC)
    (hFocus : ∀ q : focusActive (A.fibre a) (T.active.fibre a),D.extendedFocus q.val=
      T.focus.value a hF q.val.2 q.val.1 0) (hCA : (C.fibre a).carrier ⊆ (A.fibre a).carrier) :
    (T.pieceImageTemplate A C).fibre a=(D.bijection.restrict hCA).image :=
  mixedRelationImageTemplate_at_restriction C (focusComponentTransition T A) (focusComponentTransition_definable T A)
    a D.bijection hCA (focusComponentTransition_at T A a hF hC D hj hU hCoeff hFocus)

end DiamondIntegral.Section6
