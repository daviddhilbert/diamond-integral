import IntegrationSection5.CommonRectangleVolumes
import IntegrationSection5.RawKeyGammaSlices
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

theorem leftRToAmbient_range (Q : CommonProductMatching T δ hδ) (q : Q.leftAmbient)
    (hq : q.val.2 ∘ Q.leftProjection ∉ oldNLabels (T := T)) : ∃ p : Q.leftRSource, Q.leftRToAmbient p = q := by
  let q0 : Q.first.leftRHead.contractedSet := ⟨q.val,(Set.ext_iff.mp Q.first.leftR_head_slice q.val).mpr ⟨q.property,hq⟩⟩
  obtain ⟨p,hp⟩ := Q.first.leftRHead.contractionMap_surjective q0
  refine ⟨⟨p.val,p.property⟩,Subtype.ext ?_⟩
  rw [Q.leftRToAmbient_val]
  exact congrArg (fun z : Q.first.leftRHead.contractedSet => z.val) hp

theorem leftRToAmbient_graph (Q : CommonProductMatching T δ hδ) : GammaGraphDefinable G (pointMapGraph Q.leftRToAmbient) := by
  let F := Q.first.leftHead.extendBase Q.contains
  let hSub : carrier Q.leftRSource ⊆ carrier (extendBase (Q.first.left.extendBase Q.first.containsLeft).source Q.contains) := fun p hp => ((Set.ext_iff.mp Q.first.leftR_source p).mp hp).1
  have hInc : GammaGraphDefinable G (pointMapGraph (Map.inclusion hSub)) := gamma_identity_graph Q.leftRSource Q.first.leftR_gamma
  exact gamma_composition_graph (Map.inclusion hSub) F.contractionMap hInc
    (gamma_headContraction_graph F Q.first.leftHead_gamma Q.first.completeLeft.head.target_gamma)

theorem leftRFinalMap_graph (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (pointMapGraph (Q.leftRFinalMap N)) :=
  gamma_composition_graph Q.leftRToAmbient (Q.leftTail N).map Q.leftRToAmbient_graph (Q.leftTail_graph N)

def leftRFinalImage (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) := Map.image (Q.leftRFinalMap N)

def leftRRawMap (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  Map.comp (Map.toImage (rawKeyMap (Q.leftRFinalImage N))) (Map.toImage (Q.leftRFinalMap N))

theorem leftRRawMap_val (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    (Q.leftRRawMap N p).val = (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N p)).val := by
  change (rawKeyMap (Q.leftRFinalImage N) (Map.toImage (Q.leftRFinalMap N) p)).val = _
  rw [rawKeyMap_apply,rawKeyMap_apply]
  rfl

theorem leftRRawMap_surjective (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) : Function.Surjective (Q.leftRRawMap N) := by
  intro q
  obtain ⟨y,hy⟩ := rawKeyImage_surjective (Q.leftRFinalImage N) q
  obtain ⟨p,hp⟩ := y.property
  have he : Map.toImage (Q.leftRFinalMap N) p = y := Subtype.ext hp
  exact ⟨p,(congrArg (Map.toImage (rawKeyMap (Q.leftRFinalImage N))) he).trans hy⟩

theorem leftRRawMap_graph (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (rvOutputGraph (Q.leftRRawMap N)) :=
  gamma_rawKey_output (Map.toImage (Q.leftRFinalMap N)) (Q.leftRFinalMap_graph N)

def leftRProfile (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  selectedVolumeObject (Map.image (rawKeyMap (Q.leftRFinalImage N))) (Q.leftProgram N).volumeIndex

theorem leftRRawMap_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p q : Q.leftRSource) :
    Q.leftRRawMap N p = Q.leftRRawMap N q ↔
      SameRV (Q.leftRDMap p).val (Q.leftRDMap q).val ∧ SameRV (Q.leftREMap p).val (Q.leftREMap q).val := by
  rw [Subtype.ext_iff,Q.leftRRawMap_val,Q.leftRRawMap_val]
  exact Q.leftR_final_joint_kernel N p q

theorem leftRRawMap_volume (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    (rvObjectVolume (Q.leftRProfile N) (Q.leftRRawMap N p)).val =
      ![rv (vfAt (Q.leftRDMap p).val 0),rv (vfAt (Q.leftREMap p).val 0)] := by
  change (Q.leftRRawMap N p).val ∘ (Q.leftProgram N).volumeIndex = _
  rw [Q.leftRRawMap_val]
  exact Q.leftR_final_volume N p

theorem rightRToAmbient_range (Q : CommonProductMatching T δ hδ) (q : Q.rightAmbient)
    (hq : q.val.2 ∘ Q.rightProjection ∉ oldNLabels (T := T)) : ∃ p : Q.rightRSource, Q.rightRToAmbient p = q := by
  let q0 : Q.first.rightRHead.contractedSet := ⟨q.val,(Set.ext_iff.mp Q.first.rightR_head_slice q.val).mpr ⟨q.property,hq⟩⟩
  obtain ⟨p,hp⟩ := Q.first.rightRHead.contractionMap_surjective q0
  refine ⟨⟨p.val,p.property⟩,Subtype.ext ?_⟩
  rw [Q.rightRToAmbient_val]
  exact congrArg (fun z : Q.first.rightRHead.contractedSet => z.val) hp

theorem rightRToAmbient_graph (Q : CommonProductMatching T δ hδ) : GammaGraphDefinable G (pointMapGraph Q.rightRToAmbient) := by
  let F := Q.first.rightHead.extendBase Q.contains
  let hSub : carrier Q.rightRSource ⊆ carrier (extendBase (Q.first.right.extendBase Q.first.containsRight).source Q.contains) := fun p hp => ((Set.ext_iff.mp Q.first.rightR_source p).mp hp).1
  have hInc : GammaGraphDefinable G (pointMapGraph (Map.inclusion hSub)) := gamma_identity_graph Q.rightRSource Q.first.rightR_gamma
  exact gamma_composition_graph (Map.inclusion hSub) F.contractionMap hInc
    (gamma_headContraction_graph F Q.first.rightHead_gamma Q.first.completeRight.head.target_gamma)

theorem rightRFinalMap_graph (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (pointMapGraph (Q.rightRFinalMap N)) :=
  gamma_composition_graph Q.rightRToAmbient (Q.rightTail N).map Q.rightRToAmbient_graph (Q.rightTail_graph N)

def rightRFinalImage (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) := Map.image (Q.rightRFinalMap N)

def rightRRawMap (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  Map.comp (Map.toImage (rawKeyMap (Q.rightRFinalImage N))) (Map.toImage (Q.rightRFinalMap N))

theorem rightRRawMap_val (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    (Q.rightRRawMap N p).val = (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N p)).val := by
  change (rawKeyMap (Q.rightRFinalImage N) (Map.toImage (Q.rightRFinalMap N) p)).val = _
  rw [rawKeyMap_apply,rawKeyMap_apply]
  rfl

theorem rightRRawMap_surjective (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) : Function.Surjective (Q.rightRRawMap N) := by
  intro q
  obtain ⟨y,hy⟩ := rawKeyImage_surjective (Q.rightRFinalImage N) q
  obtain ⟨p,hp⟩ := y.property
  have he : Map.toImage (Q.rightRFinalMap N) p = y := Subtype.ext hp
  exact ⟨p,(congrArg (Map.toImage (rawKeyMap (Q.rightRFinalImage N))) he).trans hy⟩

theorem rightRRawMap_graph (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaGraphDefinable G (rvOutputGraph (Q.rightRRawMap N)) :=
  gamma_rawKey_output (Map.toImage (Q.rightRFinalMap N)) (Q.rightRFinalMap_graph N)

def rightRProfile (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  selectedVolumeObject (Map.image (rawKeyMap (Q.rightRFinalImage N))) (Q.rightProgram N).volumeIndex

theorem rightRRawMap_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p q : Q.rightRSource) :
    Q.rightRRawMap N p = Q.rightRRawMap N q ↔
      SameRV (Q.rightRDMap p).val (Q.rightRDMap q).val ∧ SameRV (Q.rightREMap p).val (Q.rightREMap q).val := by
  rw [Subtype.ext_iff,Q.rightRRawMap_val,Q.rightRRawMap_val]
  exact Q.rightR_final_joint_kernel N p q

theorem rightRRawMap_volume (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    (rvObjectVolume (Q.rightRProfile N) (Q.rightRRawMap N p)).val =
      ![rv (vfAt (Q.rightRDMap p).val 0),rv (vfAt (Q.rightREMap p).val 0)] := by
  change (Q.rightRRawMap N p).val ∘ (Q.rightProgram N).volumeIndex = _
  rw [Q.rightRRawMap_val]
  exact Q.rightR_final_volume N p

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
