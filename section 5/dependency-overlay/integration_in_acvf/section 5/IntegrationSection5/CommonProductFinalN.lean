import IntegrationSection5.CommonProductPrograms
import IntegrationSection5.PaddedProductInactive
import IntegrationSection5.CommonProductNComparison
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

def leftRectangleInputProjection (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  (suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘
    factorHeadProjection Q.first.completeLeft.head.projection Q.leftRectangleFirst.projection Q.leftRectangleFirst.projection_bijective) ∘
      (Fin.natAdd 1 ∘ suffixIndex Q.leftRectangleFirst.arity_le)

theorem leftN_inactiveR (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none)
    (p : N.lift.active_image) : p.val.2 ∘ Q.leftRectangleInputProjection N ∉ T.nonrectangleRVLabelsᶜ := by
  have hp := ((Set.ext_iff.mp N.active_slice p.val).mp p.property).2
  change (p.val.2 ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘
    (factorHeadProjection Q.first.completeLeft.head.projection Q.leftRectangleFirst.projection Q.leftRectangleFirst.projection_bijective ∘
      (Fin.natAdd 1 ∘ suffixIndex Q.leftRectangleFirst.arity_le)) ∉ T.nonrectangleRVLabelsᶜ
  rw [Q.first.leftR_padding_oldIndex Q.leftRectangleFirst]
  change ¬ ¬ ((p.val.2 ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘ Q.leftProjection) ∘ stripPassiveIndex T.arity ∈ T.nonrectangleRVLabels
  exact not_not.mpr hp

def leftN_sub_target (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier N.lift.active_image ⊆ carrier N.lift.target :=
  fun p hp => ((Set.ext_iff.mp N.active_slice p).mp hp).1

def leftNFinalImage (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  restrictPointImage (Q.leftRectangleCompletion N).preparation.map N.lift.active_image (Q.leftN_sub_target N)

def leftNFinalPadding (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  (Q.leftRectangleCompletion N).inactivePadding (Q.leftN_sub_target N) N.lift.active_gamma (Q.leftN_inactiveR N)

def leftNProfileIndices (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) : Fin 2 → Fin (1+N.lift.arity) :=
  ![Fin.natAdd 1 (suffixIndex N.lift.arity_le ((Fin.natAdd 1 ∘ Q.leftProjection) 0)),0]

def leftNFinalProfileIso (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  (Q.leftNFinalPadding N).profileIso
    (headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special)) ∘ Q.leftNProfileIndices N)
    (Q.leftNProfileIndices N) (fun _ => rfl)

def rightRectangleInputProjection (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  (suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘
    factorHeadProjection Q.first.completeRight.head.projection Q.rightRectangleFirst.projection Q.rightRectangleFirst.projection_bijective) ∘
      (Fin.natAdd 1 ∘ suffixIndex Q.rightRectangleFirst.arity_le)

theorem rightN_inactiveR (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none)
    (p : N.lift.active_image) : p.val.2 ∘ Q.rightRectangleInputProjection N ∉ T.nonrectangleRVLabelsᶜ := by
  have hp := ((Set.ext_iff.mp N.active_slice p.val).mp p.property).2
  change (p.val.2 ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘
    (factorHeadProjection Q.first.completeRight.head.projection Q.rightRectangleFirst.projection Q.rightRectangleFirst.projection_bijective ∘
      (Fin.natAdd 1 ∘ suffixIndex Q.rightRectangleFirst.arity_le)) ∉ T.nonrectangleRVLabelsᶜ
  rw [Q.first.rightR_padding_oldIndex Q.rightRectangleFirst]
  change ¬ ¬ ((p.val.2 ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘ Q.rightProjection) ∘ stripPassiveIndex T.arity ∈ T.nonrectangleRVLabels
  exact not_not.mpr hp

def rightN_sub_target (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier N.lift.active_image ⊆ carrier N.lift.target :=
  fun p hp => ((Set.ext_iff.mp N.active_slice p).mp hp).1

def rightNFinalImage (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  restrictPointImage (Q.rightRectangleCompletion N).preparation.map N.lift.active_image (Q.rightN_sub_target N)

def rightNFinalPadding (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  (Q.rightRectangleCompletion N).inactivePadding (Q.rightN_sub_target N) N.lift.active_gamma (Q.rightN_inactiveR N)

def rightNProfileIndices (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) : Fin 2 → Fin (1+N.lift.arity) :=
  ![Fin.natAdd 1 (suffixIndex N.lift.arity_le ((Fin.natAdd 1 ∘ Q.rightProjection) 0)),0]

def rightNFinalProfileIso (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  (Q.rightNFinalPadding N).profileIso
    (headPaddingProjection (suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special)) ∘ Q.rightNProfileIndices N)
    (Q.rightNProfileIndices N) (fun _ => rfl)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
