import IntegrationSection5.TwoBranchProgram
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

def leftRectangleFirst (Q : CommonProductMatching T δ hδ) := Classical.choice Q.first.leftR_first

def leftRectangleCompletion (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  Classical.choice (Q.left_rectangle_tail N Q.leftRectangleFirst)

def leftTail (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  pairedTailPreparation N (Q.leftRectangleCompletion N)

theorem leftTail_graph (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (pointMapGraph (Q.leftTail N).map) := pairedTailPreparation_graph N (Q.leftRectangleCompletion N)

theorem leftTail_target_gamma (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaSetDefinable G (carrier (Q.leftTail N).target) := (Q.leftRectangleCompletion N).head.target_gamma

theorem leftAmbient_eq (Q : CommonProductMatching T δ hδ) :
    Q.leftAmbient = (Q.first.leftHead.extendBase Q.contains).contractedSet := by
  apply PresentedSet.eq_of_carrier_eq
  exact (Q.first.leftHead.extendBase_contractedSet Q.contains).symm

def leftProgram (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  twoStageProgram (Q.first.leftHead.extendBase Q.contains) (Q.leftTail N) Q.leftAmbient_eq

theorem leftProgram_gamma (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaProgramDefinable G (Q.leftProgram N) := by
  apply twoStageProgram_gamma
  · exact Q.first.leftHead_gamma
  · exact Q.first.completeLeft.head.target_gamma
  · exact Q.leftTail_graph N
  · exact Q.leftTail_target_gamma N

def rightRectangleFirst (Q : CommonProductMatching T δ hδ) := Classical.choice Q.first.rightR_first

def rightRectangleCompletion (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  Classical.choice (Q.right_rectangle_tail N Q.rightRectangleFirst)

def rightTail (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  pairedTailPreparation N (Q.rightRectangleCompletion N)

theorem rightTail_graph (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (pointMapGraph (Q.rightTail N).map) := pairedTailPreparation_graph N (Q.rightRectangleCompletion N)

theorem rightTail_target_gamma (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaSetDefinable G (carrier (Q.rightTail N).target) := (Q.rightRectangleCompletion N).head.target_gamma

theorem rightAmbient_eq (Q : CommonProductMatching T δ hδ) :
    Q.rightAmbient = (Q.first.rightHead.extendBase Q.contains).contractedSet := by
  apply PresentedSet.eq_of_carrier_eq
  exact (Q.first.rightHead.extendBase_contractedSet Q.contains).symm

def rightProgram (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  twoStageProgram (Q.first.rightHead.extendBase Q.contains) (Q.rightTail N) Q.rightAmbient_eq

theorem rightProgram_gamma (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaProgramDefinable G (Q.rightProgram N) := by
  apply twoStageProgram_gamma
  · exact Q.first.rightHead_gamma
  · exact Q.first.completeRight.head.target_gamma
  · exact Q.rightTail_graph N
  · exact Q.rightTail_target_gamma N

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
