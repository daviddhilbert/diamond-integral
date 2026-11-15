import IntegrationSection5.NonrectangleHeadZero
import IntegrationSection5.MatchedHeadRV
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

def profileA (Q : NonrectangleMatchedHeads T) :=
  rawRVProjectionMap Q.completion.programA.volumeIndex (Map.image (rawKeyMap Q.unary.targetA))
def profileB (Q : NonrectangleMatchedHeads T) :=
  rawRVProjectionMap Q.completion.programB.volumeIndex (Map.image (rawKeyMap Q.unary.targetB))

theorem profileA_key_zero (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetA) :
    (Q.profileA (Map.toImage (rawKeyMap Q.unary.targetA) p)).val 0 =
      (Q.unary.specialA.inverseMap p).val.2 0 := by
  change (rawKeyMap Q.unary.targetA p).val (Q.completion.programA.volumeIndex 0) = _
  rw [Q.completion.volumeIndexA_zero,rawKeyMap_apply,Fin.append_right]
  have h := special_oldLabels Q.unary.specialA (Q.unary.specialA.inverseMap p) 0
  rw [Q.unary.specialA.apply_inverse] at h
  exact h

theorem profileB_key_zero (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetB) :
    (Q.profileB (Map.toImage (rawKeyMap Q.unary.targetB) p)).val 0 =
      (Q.unary.specialB.inverseMap p).val.2 0 := by
  change (rawKeyMap Q.unary.targetB p).val (Q.completion.programB.volumeIndex 0) = _
  rw [Q.completion.volumeIndexB_zero,rawKeyMap_apply,Fin.append_right]
  have h := special_oldLabels Q.unary.specialB (Q.unary.specialB.inverseMap p) 0
  rw [Q.unary.specialB.apply_inverse] at h
  exact h

theorem profileA_one (Q : NonrectangleMatchedHeads T) (a : rvObjectDomain (pullbackObject Q.unary.targetA)) :
    (Q.profileA a).val 1 = (rvObjectVolume (pullbackObject Q.unary.targetA) a).val 0 := by
  change a.val (Q.completion.programA.volumeIndex 1) = a.val (Fin.castAdd _ 0)
  rw [Q.completion.volumeIndexA_one]
  rfl

theorem profileB_one (Q : NonrectangleMatchedHeads T) (a : rvObjectDomain (pullbackObject Q.unary.targetB)) :
    (Q.profileB a).val 1 = (rvObjectVolume (pullbackObject Q.unary.targetB) a).val 0 := by
  change a.val (Q.completion.programB.volumeIndex 1) = a.val (Fin.castAdd _ 0)
  rw [Q.completion.volumeIndexB_one]
  rfl

theorem profile_zero_iff (Q : NonrectangleMatchedHeads T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : rvObjectDomain (pullbackObject Q.unary.targetA)) :
    (Q.profileA a).val 0 = rv (0 : VF (M := M)) ↔
      (Q.profileB (unaryIsoHomMap Q.unary.iso a)).val 0 = rv (0 : VF (M := M)) := by
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective Q.unary.targetA a
  rw [Q.unary.square,Q.profileA_key_zero,Q.profileB_key_zero]
  change (Q.unary.specialA.inverseMap p).val.2 0 = _ ↔
    (Q.unary.specialB.inverseMap (Q.unary.specialB.toMap
      (Q.unary.map (Q.unary.specialA.inverseMap p)))).val.2 0 = _
  rw [Q.unary.specialB.inverse_apply,Q.unary.map_spec]
  exact Q.first.headIso_head_zero_iff δ hδ ⟨(Q.unary.specialA.inverseMap p).val,
    (Set.ext_iff.mp Q.unary.sourceA_eq _).mp (Q.unary.specialA.inverseMap p).property⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
