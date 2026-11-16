import «section 6».FocusComponentTemplateRealizations

/-! The template's full zero-extended scalar code equals the actual
component's extended focus on its complete current source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem componentTemplateFocusExtension
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) (hF : a ∈ T.focus.good)
    (D : CentripetalData (G := G) (A.fibre a)) (hU : D.activeTags=T.active.fibre a)
    (hFocus : ∀ q : focusActive (A.fibre a) (T.active.fibre a),D.extendedFocus q.val=
      T.focus.value a hF q.val.2 q.val.1 0)
    (x : Mixed M n r) (hx : x ∈ (A.fibre a).carrier) :
    scalarCodeExtension (rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a))
      (T.focus.value a hF) (T.focus.family_graph_definable a hF)) (mixedValues x)=(D.extendedFocus x).val := by
  let f := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a))
    (T.focus.value a hF) (T.focus.family_graph_definable a hF)
  change scalarCodeExtension f (mixedValues x)=(D.extendedFocus x).val
  by_cases hu : x.2 ∈ (T.active.fibre a).carrier
  · let q : focusActive (A.fibre a) (T.active.fibre a) := ⟨x,hx,hu⟩
    exact (scalarCodeExtension_at f q).trans (congrArg Subtype.val (hFocus q)).symm
  · have huD : x.2 ∉ D.activeTags.carrier := by simpa only [hU] using hu
    have hNo : mixedValues x ∉ (rawMixedSpace n r).preimage (focusActive (A.fibre a) (T.active.fibre a)).carrier := by
      rintro ⟨hz,hActive⟩
      have hxActive : x ∈ (focusActive (A.fibre a) (T.active.fibre a)).carrier := by
        simpa only [decode_mixedValues] using hActive
      exact hu hxActive.2
    rw [scalarCodeExtension,dite_eq_right hNo,D.extendedFocus_inactive huD]
    rfl

end DiamondIntegral.Section6
