import IntegrationSection5.CommonRectangleInputs
import IntegrationSection5.CommonProductFinalN
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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

theorem leftOriginalIndex (Q : CommonProductMatching T δ hδ) :
    Q.leftProjection ∘ stripPassiveIndex T.arity =
      Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le Q.first.leftHead.special) := by
  funext j
  change headPaddingProjection (suffixIndex (specialRelative_rvArity_le Q.first.completeLeft.preparation.special))
    (Fin.natAdd 1 (Fin.natAdd 1 j)) = _
  rw [headPaddingProjection,Fin.append_right]
  apply Fin.ext
  change 1 + (Q.first.completeLeft.preparation.arity - (1+T.arity) + (1+j.val)) =
    1 + (Q.first.completeLeft.preparation.arity - T.arity + j.val)
  have hle := specialRelative_rvArity_le Q.first.completeLeft.preparation.special
  change 1+T.arity ≤ Q.first.completeLeft.preparation.arity at hle
  omega

theorem leftRToAmbient_labels (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    (Q.leftRToAmbient p).val.2 ∘ (Q.leftProjection ∘ stripPassiveIndex T.arity) = p.val.2 := by
  rw [Q.leftRToAmbient_val,Q.leftOriginalIndex]
  funext j
  change (headKeyMap Q.first.leftRHead.target (Q.first.leftRHead.map ⟨p.val,p.property⟩)).val.2
    (Fin.natAdd 1 (suffixIndex _ j)) = p.val.2 j
  rw [headKeyMap_apply]
  simp only [headKey,Fin.append_right]
  exact specialRelative_oldLabels Q.first.leftRHead.special ⟨p.val,p.property⟩ j

def leftRPreFinal (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    Map Q.leftRSource (Q.leftRectangleCompletion N).prefixTarget :=
  Map.comp (Q.leftRectangleCompletion N).preMap (Map.comp N.map Q.leftRToAmbient)

theorem leftRPreFinal_vf (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    vfAt (Q.leftRPreFinal N p).val 0 = vfAt p.val 1 := by
  change vfAt ((Q.leftRectangleCompletion N).preMap (N.map (Q.leftRToAmbient p))).val 0 = _
  rw [(Q.leftRectangleCompletion N).prefix_formula]
  change vfAt (N.map (Q.leftRToAmbient p)).val 0 = _
  rw [N.inactive_vf (Q.leftRToAmbient p) (Q.leftRToAmbient_offN p),Q.leftRToAmbient_vf]

theorem leftRPreFinal_labels (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    (Q.leftRPreFinal N p).val.2 ∘ (Fin.natAdd 1 ∘ Q.leftRectangleInputProjection N) = p.val.2 := by
  change ((Q.leftRectangleCompletion N).preMap (N.map (Q.leftRToAmbient p))).val.2 ∘ _ = _
  rw [(Q.leftRectangleCompletion N).prefix_formula]
  have h := congrArg (fun s => s ∘ Q.leftRectangleInputProjection N)
    (coordinateCanonical_oldRV 0 (N.map (Q.leftRToAmbient p)).val)
  refine h.trans ?_
  change (((N.map (Q.leftRToAmbient p)).val.2 ∘
    suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘
      (factorHeadProjection Q.first.completeLeft.head.projection Q.leftRectangleFirst.projection Q.leftRectangleFirst.projection_bijective ∘
        (Fin.natAdd 1 ∘ suffixIndex Q.leftRectangleFirst.arity_le))) = p.val.2
  rw [N.oldLabels,Q.first.leftR_padding_oldIndex Q.leftRectangleFirst]
  exact Q.leftRToAmbient_labels p

theorem leftRPreFinal_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p q : Q.leftRSource) :
    SameRV (Q.leftRPreFinal N p).val (Q.leftRPreFinal N q).val ↔
      rv (vfAt p.val 1) = rv (vfAt q.val 1) ∧ SameRV (Q.leftRDMap p).val (Q.leftRDMap q).val := by
  change SameRV ((Q.leftRectangleCompletion N).preMap (N.map (Q.leftRToAmbient p))).val
    ((Q.leftRectangleCompletion N).preMap (N.map (Q.leftRToAmbient q))).val ↔ _
  rw [(Q.leftRectangleCompletion N).prefix_formula,(Q.leftRectangleCompletion N).prefix_formula,
    RVProjectionPadding.canonical_sameRV_iff]
  exact (sameRV_pair_of_fixedVF (Q.leftRToAmbient p).val (Q.leftRToAmbient q).val
    (N.map (Q.leftRToAmbient p)).val (N.map (Q.leftRToAmbient q)).val _
    (N.inactive_vf _ (Q.leftRToAmbient_offN p)) (N.inactive_vf _ (Q.leftRToAmbient_offN q))
    (N.oldLabels _) (N.oldLabels _) (N.inactive_sameRV _ _ (Q.leftRToAmbient_offN p) (Q.leftRToAmbient_offN q))).trans
      (Q.leftRToAmbient_kernel p q)

theorem rightOriginalIndex (Q : CommonProductMatching T δ hδ) :
    Q.rightProjection ∘ stripPassiveIndex T.arity =
      Fin.natAdd 1 ∘ suffixIndex (specialRelative_rvArity_le Q.first.rightHead.special) := by
  funext j
  change headPaddingProjection (suffixIndex (specialRelative_rvArity_le Q.first.completeRight.preparation.special))
    (Fin.natAdd 1 (Fin.natAdd 1 j)) = _
  rw [headPaddingProjection,Fin.append_right]
  apply Fin.ext
  change 1 + (Q.first.completeRight.preparation.arity - (1+T.arity) + (1+j.val)) =
    1 + (Q.first.completeRight.preparation.arity - T.arity + j.val)
  have hle := specialRelative_rvArity_le Q.first.completeRight.preparation.special
  change 1+T.arity ≤ Q.first.completeRight.preparation.arity at hle
  omega

theorem rightRToAmbient_labels (Q : CommonProductMatching T δ hδ) (p : Q.rightRSource) :
    (Q.rightRToAmbient p).val.2 ∘ (Q.rightProjection ∘ stripPassiveIndex T.arity) = p.val.2 := by
  rw [Q.rightRToAmbient_val,Q.rightOriginalIndex]
  funext j
  change (headKeyMap Q.first.rightRHead.target (Q.first.rightRHead.map ⟨p.val,p.property⟩)).val.2
    (Fin.natAdd 1 (suffixIndex _ j)) = p.val.2 j
  rw [headKeyMap_apply]
  simp only [headKey,Fin.append_right]
  exact specialRelative_oldLabels Q.first.rightRHead.special ⟨p.val,p.property⟩ j

def rightRPreFinal (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    Map Q.rightRSource (Q.rightRectangleCompletion N).prefixTarget :=
  Map.comp (Q.rightRectangleCompletion N).preMap (Map.comp N.map Q.rightRToAmbient)

theorem rightRPreFinal_vf (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    vfAt (Q.rightRPreFinal N p).val 0 = vfAt p.val 1 := by
  change vfAt ((Q.rightRectangleCompletion N).preMap (N.map (Q.rightRToAmbient p))).val 0 = _
  rw [(Q.rightRectangleCompletion N).prefix_formula]
  change vfAt (N.map (Q.rightRToAmbient p)).val 0 = _
  rw [N.inactive_vf (Q.rightRToAmbient p) (Q.rightRToAmbient_offN p),Q.rightRToAmbient_vf]

theorem rightRPreFinal_labels (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    (Q.rightRPreFinal N p).val.2 ∘ (Fin.natAdd 1 ∘ Q.rightRectangleInputProjection N) = p.val.2 := by
  change ((Q.rightRectangleCompletion N).preMap (N.map (Q.rightRToAmbient p))).val.2 ∘ _ = _
  rw [(Q.rightRectangleCompletion N).prefix_formula]
  have h := congrArg (fun s => s ∘ Q.rightRectangleInputProjection N)
    (coordinateCanonical_oldRV 0 (N.map (Q.rightRToAmbient p)).val)
  refine h.trans ?_
  change (((N.map (Q.rightRToAmbient p)).val.2 ∘
    suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special))) ∘
      (factorHeadProjection Q.first.completeRight.head.projection Q.rightRectangleFirst.projection Q.rightRectangleFirst.projection_bijective ∘
        (Fin.natAdd 1 ∘ suffixIndex Q.rightRectangleFirst.arity_le))) = p.val.2
  rw [N.oldLabels,Q.first.rightR_padding_oldIndex Q.rightRectangleFirst]
  exact Q.rightRToAmbient_labels p

theorem rightRPreFinal_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p q : Q.rightRSource) :
    SameRV (Q.rightRPreFinal N p).val (Q.rightRPreFinal N q).val ↔
      rv (vfAt p.val 1) = rv (vfAt q.val 1) ∧ SameRV (Q.rightRDMap p).val (Q.rightRDMap q).val := by
  change SameRV ((Q.rightRectangleCompletion N).preMap (N.map (Q.rightRToAmbient p))).val
    ((Q.rightRectangleCompletion N).preMap (N.map (Q.rightRToAmbient q))).val ↔ _
  rw [(Q.rightRectangleCompletion N).prefix_formula,(Q.rightRectangleCompletion N).prefix_formula,
    RVProjectionPadding.canonical_sameRV_iff]
  exact (sameRV_pair_of_fixedVF (Q.rightRToAmbient p).val (Q.rightRToAmbient q).val
    (N.map (Q.rightRToAmbient p)).val (N.map (Q.rightRToAmbient q)).val _
    (N.inactive_vf _ (Q.rightRToAmbient_offN p)) (N.inactive_vf _ (Q.rightRToAmbient_offN q))
    (N.oldLabels _) (N.oldLabels _) (N.inactive_sameRV _ _ (Q.rightRToAmbient_offN p) (Q.rightRToAmbient_offN q))).trans
      (Q.rightRToAmbient_kernel p q)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
