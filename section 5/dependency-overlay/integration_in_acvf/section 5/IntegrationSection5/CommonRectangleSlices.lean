import IntegrationSection5.CommonRectanglePadding
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

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

theorem leftR_head_slice (P : CommonProductHeadPair T) :
    carrier P.leftRHead.contractedSet = {p | p ∈ carrier P.leftHead.contractedSet ∧
      p.2 ∘ headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∈
        {s | s ∘ stripPassiveIndex T.arity ∉ T.nonrectangleRVLabels}} := by
  have h := P.leftHead.rvSliceImage T.nonrectangleRVLabelsᶜ P.leftR_source
  have hh := headImage_rvSlice (suffixIndex (specialRelative_rvArity_le P.leftHead.special))
    T.nonrectangleRVLabelsᶜ h
  ext p
  have he := Set.ext_iff.mp hh p
  change (p ∈ carrier P.leftRHead.contractedSet) ↔
    (p ∈ carrier P.leftHead.contractedSet ∧
      p.2 ∘ (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le P.leftHead.special)) ∈ T.nonrectangleRVLabelsᶜ) at he
  have hIdx : (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le P.leftHead.special)) =
      headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∘
        stripPassiveIndex T.arity := by
    funext j
    change Fin.natAdd 1 (suffixIndex _ j) =
      headPaddingProjection _ (Fin.natAdd 1 (Fin.natAdd 1 j))
    rw [headPaddingProjection,Fin.append_right]
    apply Fin.ext
    simp only [suffixIndex,Fin.coe_natAdd,Fin.val_mk,Function.comp_apply]
    change 1 + (P.completeLeft.preparation.arity - T.arity + j.val) =
      1 + (P.completeLeft.preparation.arity - (1 + T.arity) + (1 + j.val))
    have hle := specialRelative_rvArity_le P.completeLeft.preparation.special
    change 1 + T.arity ≤ P.completeLeft.preparation.arity at hle
    omega
  rw [hIdx] at he
  exact he

theorem rightR_head_slice (P : CommonProductHeadPair T) :
    carrier P.rightRHead.contractedSet = {p | p ∈ carrier P.rightHead.contractedSet ∧
      p.2 ∘ headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∈
        {s | s ∘ stripPassiveIndex T.arity ∉ T.nonrectangleRVLabels}} := by
  have h := P.rightHead.rvSliceImage T.nonrectangleRVLabelsᶜ P.rightR_source
  have hh := headImage_rvSlice (suffixIndex (specialRelative_rvArity_le P.rightHead.special))
    T.nonrectangleRVLabelsᶜ h
  ext p
  have he := Set.ext_iff.mp hh p
  change (p ∈ carrier P.rightRHead.contractedSet) ↔
    (p ∈ carrier P.rightHead.contractedSet ∧
      p.2 ∘ (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le P.rightHead.special)) ∈ T.nonrectangleRVLabelsᶜ) at he
  have hIdx : (Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le P.rightHead.special)) =
      headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∘
        stripPassiveIndex T.arity := by
    funext j
    change Fin.natAdd 1 (suffixIndex _ j) =
      headPaddingProjection _ (Fin.natAdd 1 (Fin.natAdd 1 j))
    rw [headPaddingProjection,Fin.append_right]
    apply Fin.ext
    simp only [suffixIndex,Fin.coe_natAdd,Fin.val_mk,Function.comp_apply]
    change 1 + (P.completeRight.preparation.arity - T.arity + j.val) =
      1 + (P.completeRight.preparation.arity - (1 + T.arity) + (1 + j.val))
    have hle := specialRelative_rvArity_le P.completeRight.preparation.special
    change 1 + T.arity ≤ P.completeRight.preparation.arity at hle
    omega
  rw [hIdx] at he
  exact he

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
