import «section 6».UnaryPreparationContexts
import «section 6».SimultaneousFocusSteps
import «section 6».CentripetalPullbackPreservation
import «section 6».RefinedLabelCentripetalMaps

/-! Exact compatibility of a unary focus with its actual ambient
realization. Both the branch flag and the new leading-term label are
retained; all other VF coordinates are fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {i : Fin m}

theorem RVFocusRealization.context_extendedFocus
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A)
    (F : RVFocusRealization (G := G) D.toRVFocusData)
    (H : RVFocusRealization (G := G) (X.focusData D)) (p : X.source) :
    H.component.extendedFocus p.val = F.component.extendedFocus (X.projection p).val := by
  by_cases hu : p.val.2 ∘ X.labels ∈ D.activeTags.carrier
  · have hH : p.val.2 ∈ H.component.activeTags.carrier := by rw [H.activeTags]; exact hu
    have hF : (X.projection p).val.2 ∈ F.component.activeTags.carrier := by
      rw [F.activeTags,X.projection_value]; exact hu
    rw [H.component.extendedFocus_active p.property hH,
      F.component.extendedFocus_active (X.projection p).property hF,H.focus,F.focus]
    exact congrArg D.focus (congrArg Prod.snd (X.projection_value p)).symm
  · have hH : p.val.2 ∉ H.component.activeTags.carrier := by rw [H.activeTags]; exact hu
    have hF : (X.projection p).val.2 ∉ F.component.activeTags.carrier := by
      rw [F.activeTags,X.projection_value]; exact hu
    rw [H.component.extendedFocus_inactive hH,F.component.extendedFocus_inactive hF]

theorem RVFocusRealization.context_point
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A)
    (F : RVFocusRealization (G := G) D.toRVFocusData)
    (H : RVFocusRealization (G := G) (X.focusData D))
    (hCoeff : H.component.coefficient = F.component.coefficient) (p : X.source) :
    ((fun _ : Fin 1 => (H.component.point p.val).1 i),
      (H.component.point p.val).2 ∘ prefixLabelSelection X.labels) =
        F.component.point (X.projection p).val := by
  have hExt := RVFocusRealization.context_extendedFocus X D F H p
  have hCore : H.component.core p.val = F.component.core (X.projection p).val := by
    simp only [CentripetalData.core,hCoeff,hExt,H.coordinate,F.coordinate,X.projection_value]
    rfl
  apply Prod.ext
  · funext j
    fin_cases j
    simp only [CentripetalData.point,H.coordinate,F.coordinate,X.projection_value,
      UnaryPreparationContext.focusData,UnaryFocusData.toRVFocusData,
      Function.update_self,hExt,hCore,hCoeff]
    rfl
  · simp only [CentripetalData.point,hCore,append_prefixLabelSelection,X.projection_value]

def UnaryPreparationContext.nextLabels (X : UnaryPreparationContext A i) :
    Fin (1+(1+r)) → Fin (m+(1+X.arity)) :=
  Fin.addCases (fun _ => Fin.castAdd (1+X.arity) i)
    (fun j => Fin.natAdd m (prefixLabelSelection X.labels j))

theorem RVFocusRealization.context_regularized_point
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A)
    (F : RVFocusRealization (G := G) D.toRVFocusData)
    (H : RVFocusRealization (G := G) (X.focusData D))
    (hCoeff : H.component.coefficient = F.component.coefficient) (p : X.source) :
    ((fun _ : Fin 1 => (regularize (H.component.point p.val)).1 i),
      (regularize (H.component.point p.val)).2 ∘ X.nextLabels) =
        regularize (F.component.point (X.projection p).val) := by
  have hPoint := RVFocusRealization.context_point X D F H hCoeff p
  apply Prod.ext
  · change (fun _ : Fin 1 => (H.component.point p.val).1 i)=(F.component.point (X.projection p).val).1
    exact congrArg Prod.fst hPoint
  · funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [regularize,Function.comp_apply,UnaryPreparationContext.nextLabels,
        Fin.addCases_left,Fin.append_left]
      exact congrArg (rv M) (congrFun (congrArg Prod.fst hPoint) j)
    · simp only [regularize,Function.comp_apply,UnaryPreparationContext.nextLabels,
        Fin.addCases_right,Fin.append_right]
      exact congrFun (congrArg Prod.snd hPoint) j

theorem RVFocusRealization.context_fixed_coordinate
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A)
    (H : RVFocusRealization (G := G) (X.focusData D))
    (p : X.source) (j : Fin m) (hj : j ≠ i) :
    (centripetalStepMap H.component p).val.1 j=p.val.1 j := by
  change (H.component.point p.val).1 j=p.val.1 j
  simp only [CentripetalData.point,H.coordinate,UnaryPreparationContext.focusData,Function.update_of_ne hj]

end DiamondIntegral.Section6
