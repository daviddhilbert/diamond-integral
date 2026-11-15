import IntegrationSection5.CommonRectangleJoint
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

theorem leftR_first_volume (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    (Q.leftRToAmbient p).val.2 0 = rv (vfAt (Q.leftRDMap p).val 0) := by
  let a : Q.first.rectangle.source := ⟨p.val,p.property⟩
  have h := Q.first.completeLeft.head.square (Q.first.leftR_preMap a) (Q.first.leftR_preMap_flag a)
  have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (Q.first.leftR_preMap a).val,
      Q.first.completeLeft.head.embedding _ (Q.first.leftR_preMap a).property (Q.first.leftR_preMap_flag a)⟩ :
        Q.first.rectangle.sourceD) = Q.first.leftR_dSource a :=
    Subtype.ext (Q.first.leftR_preMap_select a).symm
  rw [he] at h
  have hv := congrArg (fun q : Point (M := M) 1 Q.first.rectangle.arityD => rv (vfAt q 0)) h
  rw [Q.leftRToAmbient_val]
  change (headKeyMap Q.first.leftRHead.target (Q.first.leftRHead.map a)).val.2 0 = _
  rw [headKeyMap_apply]
  exact hv

theorem leftProgram_volume_zero (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    (Q.leftProgram N).volumeIndex 0 = Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le (Q.leftTail N).special) 0) := by
  apply Fin.ext
  change (1+(Q.leftTail N).arity) - (1+Q.first.leftHead.arity) + 0 =
    1 + ((Q.leftTail N).arity - (1+Q.first.leftHead.arity) + 0)
  have hle := specialRelative_rvArity_le (Q.leftTail N).special
  change 1+Q.first.leftHead.arity ≤ (Q.leftTail N).arity at hle
  omega

theorem leftProgram_volume_one (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    (Q.leftProgram N).volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+(Q.leftTail N).arity) - (1+(Q.leftTail N).arity) + 0 = 0
  omega

theorem leftR_final_volume (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N p)).val ∘ (Q.leftProgram N).volumeIndex =
      ![rv (vfAt (Q.leftRDMap p).val 0),rv (vfAt (Q.leftREMap p).val 0)] := by
  funext i
  fin_cases i
  · change (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N p)).val ((Q.leftProgram N).volumeIndex 0) = _
    rw [Q.leftProgram_volume_zero,rawKeyMap_apply]
    rw [Fin.append_right]
    change ((Q.leftTail N).map (Q.leftRToAmbient p)).val.2
      (suffixIndex (specialRelative_rvArity_le (Q.leftTail N).special) 0) = _
    exact (specialRelative_oldLabels (Q.leftTail N).special (Q.leftRToAmbient p) 0).trans (Q.leftR_first_volume p)
  · change (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N p)).val ((Q.leftProgram N).volumeIndex 1) = _
    rw [Q.leftProgram_volume_one,rawKeyMap_apply]
    change rv (vfAt (Q.leftRFinalMap N p).val 0) = rv (vfAt (Q.leftREMap p).val 0)
    exact congrArg (fun q : Point (M := M) 1 Q.first.rectangle.arityE => rv (vfAt q 0)) (Q.leftR_final_factor N p)

theorem rightR_first_volume (Q : CommonProductMatching T δ hδ) (p : Q.rightRSource) :
    (Q.rightRToAmbient p).val.2 0 = rv (vfAt (Q.rightRDMap p).val 0) := by
  let a : Q.first.rectangle.swap.source := ⟨p.val,p.property⟩
  have h := Q.first.completeRight.head.square (Q.first.rightR_preMap a) (Q.first.rightR_preMap_flag a)
  have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (Q.first.rightR_preMap a).val,
      Q.first.completeRight.head.embedding _ (Q.first.rightR_preMap a).property (Q.first.rightR_preMap_flag a)⟩ :
        Q.first.rectangle.sourceE) = Q.first.rightR_dSource a :=
    Subtype.ext (Q.first.rightR_preMap_select a).symm
  rw [he] at h
  have hv := congrArg (fun q : Point (M := M) 1 Q.first.rectangle.arityE => rv (vfAt q 0)) h
  rw [Q.rightRToAmbient_val]
  change (headKeyMap Q.first.rightRHead.target (Q.first.rightRHead.map a)).val.2 0 = _
  rw [headKeyMap_apply]
  exact hv

theorem rightProgram_volume_zero (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    (Q.rightProgram N).volumeIndex 0 = Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le (Q.rightTail N).special) 0) := by
  apply Fin.ext
  change (1+(Q.rightTail N).arity) - (1+Q.first.rightHead.arity) + 0 =
    1 + ((Q.rightTail N).arity - (1+Q.first.rightHead.arity) + 0)
  have hle := specialRelative_rvArity_le (Q.rightTail N).special
  change 1+Q.first.rightHead.arity ≤ (Q.rightTail N).arity at hle
  omega

theorem rightProgram_volume_one (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    (Q.rightProgram N).volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+(Q.rightTail N).arity) - (1+(Q.rightTail N).arity) + 0 = 0
  omega

theorem rightR_final_volume (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N p)).val ∘ (Q.rightProgram N).volumeIndex =
      ![rv (vfAt (Q.rightRDMap p).val 0),rv (vfAt (Q.rightREMap p).val 0)] := by
  funext i
  fin_cases i
  · change (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N p)).val ((Q.rightProgram N).volumeIndex 0) = _
    rw [Q.rightProgram_volume_zero,rawKeyMap_apply]
    rw [Fin.append_right]
    change ((Q.rightTail N).map (Q.rightRToAmbient p)).val.2
      (suffixIndex (specialRelative_rvArity_le (Q.rightTail N).special) 0) = _
    exact (specialRelative_oldLabels (Q.rightTail N).special (Q.rightRToAmbient p) 0).trans (Q.rightR_first_volume p)
  · change (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N p)).val ((Q.rightProgram N).volumeIndex 1) = _
    rw [Q.rightProgram_volume_one,rawKeyMap_apply]
    change rv (vfAt (Q.rightRFinalMap N p).val 0) = rv (vfAt (Q.rightREMap p).val 0)
    exact congrArg (fun q : Point (M := M) 1 Q.first.rectangle.arityD => rv (vfAt q 0)) (Q.rightR_final_factor N p)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
