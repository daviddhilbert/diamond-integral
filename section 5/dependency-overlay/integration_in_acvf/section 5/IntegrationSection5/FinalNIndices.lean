import IntegrationSection5.FinalNComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

theorem leftNFinalIndices (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special)) ∘
      Q.leftNProfileIndices N = (Q.leftProgram N).volumeIndex := by
  have hρ : Q.leftProjection (0 : Fin (1+(1+T.arity))) = 0 :=
    Fin.append_left (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le Q.first.completeLeft.preparation.special)) (0 : Fin 1)
  funext i
  fin_cases i
  · apply Fin.ext
    change (headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special))
      (Fin.natAdd 1 (suffixIndex N.lift.arity_le ((Fin.natAdd 1 ∘ Q.leftProjection) 0)))).val = _
    rw [headPaddingProjection,Fin.append_right]
    change 1 + ((Q.leftRectangleCompletion N).preparation.arity - N.lift.arity +
      (N.lift.arity - (1+(1+Q.first.leftHead.arity)) + (1+(Q.leftProjection 0).val))) =
        (1+(Q.leftRectangleCompletion N).preparation.arity) - (1+Q.first.leftHead.arity) + 0
    rw [hρ]
    have hN := N.lift.arity_le
    have hR := specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special
    change 1+(1+Q.first.leftHead.arity) ≤ N.lift.arity at hN
    change N.lift.arity ≤ (Q.leftRectangleCompletion N).preparation.arity at hR
    simp only [Fin.val_zero]
    omega
  · apply Fin.ext
    change 0 = (1+(Q.leftRectangleCompletion N).preparation.arity) - (1+(Q.leftRectangleCompletion N).preparation.arity) + 0
    omega

theorem rightNFinalIndices (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special)) ∘
      Q.rightNProfileIndices N = (Q.rightProgram N).volumeIndex := by
  have hρ : Q.rightProjection (0 : Fin (1+(1+T.arity))) = 0 :=
    Fin.append_left (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le Q.first.completeRight.preparation.special)) (0 : Fin 1)
  funext i
  fin_cases i
  · apply Fin.ext
    change (headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special))
      (Fin.natAdd 1 (suffixIndex N.lift.arity_le ((Fin.natAdd 1 ∘ Q.rightProjection) 0)))).val = _
    rw [headPaddingProjection,Fin.append_right]
    change 1 + ((Q.rightRectangleCompletion N).preparation.arity - N.lift.arity +
      (N.lift.arity - (1+(1+Q.first.rightHead.arity)) + (1+(Q.rightProjection 0).val))) =
        (1+(Q.rightRectangleCompletion N).preparation.arity) - (1+Q.first.rightHead.arity) + 0
    rw [hρ]
    have hN := N.lift.arity_le
    have hR := specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special
    change 1+(1+Q.first.rightHead.arity) ≤ N.lift.arity at hN
    change N.lift.arity ≤ (Q.rightRectangleCompletion N).preparation.arity at hR
    simp only [Fin.val_zero]
    omega
  · apply Fin.ext
    change 0 = (1+(Q.rightRectangleCompletion N).preparation.arity) - (1+(Q.rightRectangleCompletion N).preparation.arity) + 0
    omega

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
