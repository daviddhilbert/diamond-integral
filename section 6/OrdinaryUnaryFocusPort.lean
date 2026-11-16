import «section 6».OrdinaryFocusTagDomains

/-! An actual ordinary unary focus, pulled back to a proper current
source with arbitrary extra RV labels, supplies full UnaryFocusData
over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)

def focus (u : Fin q → RVInfinity M) : VF M :=
  if h : ∃ p : focusActive X.source (X.activeTags D hD),p.val.2=u then
    (X.scalarMap D hD h.choose).val 0 else 0

theorem focus_at (p : focusActive X.source (X.activeTags D hD)) :
    X.focus D hD p.val.2=(X.scalarMap D hD p).val 0 := by
  have hp : ∃ a : focusActive X.source (X.activeTags D hD),a.val.2=p.val.2 := ⟨p,rfl⟩
  rw [focus,dif_pos hp]
  exact X.scalarMap_same_labels D hD hp.choose p hp.choose_spec

def focusData : UnaryFocusData X.source where
  activeTags := X.activeTags D hD
  focus := X.focus D hD
  focusMap := X.scalarMap D hD
  focusMap_eq p := (X.focus_at D hD p).symm
  sourceProper := X.proper
  sourceDoublyBounded := X.doublyBounded
  tagged := X.tagged
  focusRV p hp hu := by
    rw [X.focus_at D hD ⟨p,hp,hu⟩,X.scalarMap_value]
    have h := OriginalBaseOrdinaryFocus.center_leading_term D
      (X.oldMap ⟨p,hp⟩).val (X.oldActiveMap D hD ⟨p,hp,hu⟩).property
    exact h.trans (congrArg (fun z : Mixed M 1 r => rv M (z.1 0)) (X.point ⟨p,hp⟩))

theorem focusData_value (p : X.source) (hu : p.val.2 ∈ (X.activeTags D hD).carrier) :
    (X.focusData D hD).focus p.val.2=D.center (X.oldMap p).val :=
  (X.focus_at D hD ⟨p.val,p.property,hu⟩).trans (X.scalarMap_value D hD _)

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
