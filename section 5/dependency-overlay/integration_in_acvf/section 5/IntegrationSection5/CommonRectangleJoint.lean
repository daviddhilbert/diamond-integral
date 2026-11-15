import IntegrationSection5.CommonRectangleFinalInputs
import IntegrationSection5.RVContractionMaps
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

theorem leftRPreFinal_select (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    activeUnaryProjection 0 (Fin.natAdd 1 ∘ Q.leftRectangleInputProjection N) (Q.leftRPreFinal N p).val =
      (Q.leftRESource p).val := by
  refine Prod.ext ?_ (Q.leftRPreFinal_labels N p)
  funext i
  fin_cases i
  exact Q.leftRPreFinal_vf N p

theorem leftRPreFinal_flag (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    (Q.leftRPreFinal N p).val.2 ∘ (Fin.natAdd 1 ∘ Q.leftRectangleInputProjection N) ∈ T.nonrectangleRVLabelsᶜ := by
  rw [Q.leftRPreFinal_labels]
  exact ((Set.ext_iff.mp Q.first.leftR_source p.val).mp p.property).2

theorem leftR_final_factor (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftRSource) :
    activeUnaryProjection 0 (Q.leftRectangleCompletion N).head.projection
      ((Q.leftRectangleCompletion N).head.preparation.map (Q.leftRPreFinal N p)).val = (Q.leftREMap p).val := by
  have h := (Q.leftRectangleCompletion N).head.square (Q.leftRPreFinal N p) (Q.leftRPreFinal_flag N p)
  have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Q.leftRectangleInputProjection N) (Q.leftRPreFinal N p).val,
      (Q.leftRectangleCompletion N).head.embedding _ (Q.leftRPreFinal N p).property (Q.leftRPreFinal_flag N p)⟩ :
        extendBase Q.first.rectangle.sourceE Q.contains) = Q.leftRESource p :=
    Subtype.ext (Q.leftRPreFinal_select N p)
  exact h.trans (congrArg (fun z : extendBase Q.first.rectangle.sourceE Q.contains =>
    ((Q.first.rectangle.specialE.extendBase Q.contains).toMap z).val) he)

theorem leftRE_inverse_class (Q : CommonProductMatching T δ hδ) (p q : Q.leftRSource)
    (he : SameRV (Q.leftREMap p).val (Q.leftREMap q).val) : rv (vfAt p.val 1) = rv (vfAt q.val 1) := by
  let u := Q.first.rectangle.specialE.extendBase Q.contains
  have h := u.inverse_contractible (u.toMap (Q.leftRESource p)) (u.toMap (Q.leftRESource q)) he
  rw [u.inverse_apply,u.inverse_apply] at h
  exact ((sameRV_iff _ _).mp h).1 0

def leftRFinalMap (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    Map Q.leftRSource (Q.leftTail N).target := Map.comp (Q.leftTail N).map Q.leftRToAmbient

theorem leftR_final_joint_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p q : Q.leftRSource) :
    (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N p)).val =
      (rawKeyMap (Q.leftTail N).target (Q.leftRFinalMap N q)).val ↔
        SameRV (Q.leftRDMap p).val (Q.leftRDMap q).val ∧ SameRV (Q.leftREMap p).val (Q.leftREMap q).val := by
  rw [rawKeyMap_eq_iff]
  rw [← unary_headKey_eq_iff_sameRV]
  exact lifted_unary_joint_kernel (Q.leftRectangleCompletion N).head.preparation.map
    (Q.leftRectangleCompletion N).head.preparation.special (Q.leftRectangleCompletion N).head.arity_le
    (Q.leftRectangleCompletion N).head.projection (Q.leftRectangleCompletion N).head.coverage
    (Q.leftRPreFinal N) Q.leftRDMap Q.leftREMap (fun p => vfAt p.val 1)
    (Q.leftRPreFinal_vf N) (Q.leftRPreFinal_kernel N) (Q.leftR_final_factor N) Q.leftRE_inverse_class p q

theorem rightRPreFinal_select (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    activeUnaryProjection 0 (Fin.natAdd 1 ∘ Q.rightRectangleInputProjection N) (Q.rightRPreFinal N p).val =
      (Q.rightRESource p).val := by
  refine Prod.ext ?_ (Q.rightRPreFinal_labels N p)
  funext i
  fin_cases i
  exact Q.rightRPreFinal_vf N p

theorem rightRPreFinal_flag (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    (Q.rightRPreFinal N p).val.2 ∘ (Fin.natAdd 1 ∘ Q.rightRectangleInputProjection N) ∈ T.nonrectangleRVLabelsᶜ := by
  rw [Q.rightRPreFinal_labels]
  exact ((Set.ext_iff.mp Q.first.rightR_source p.val).mp p.property).2

theorem rightR_final_factor (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightRSource) :
    activeUnaryProjection 0 (Q.rightRectangleCompletion N).head.projection
      ((Q.rightRectangleCompletion N).head.preparation.map (Q.rightRPreFinal N p)).val = (Q.rightREMap p).val := by
  have h := (Q.rightRectangleCompletion N).head.square (Q.rightRPreFinal N p) (Q.rightRPreFinal_flag N p)
  have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Q.rightRectangleInputProjection N) (Q.rightRPreFinal N p).val,
      (Q.rightRectangleCompletion N).head.embedding _ (Q.rightRPreFinal N p).property (Q.rightRPreFinal_flag N p)⟩ :
        extendBase Q.first.rectangle.sourceD Q.contains) = Q.rightRESource p :=
    Subtype.ext (Q.rightRPreFinal_select N p)
  exact h.trans (congrArg (fun z : extendBase Q.first.rectangle.sourceD Q.contains =>
    ((Q.first.rectangle.specialD.extendBase Q.contains).toMap z).val) he)

theorem rightRE_inverse_class (Q : CommonProductMatching T δ hδ) (p q : Q.rightRSource)
    (he : SameRV (Q.rightREMap p).val (Q.rightREMap q).val) : rv (vfAt p.val 1) = rv (vfAt q.val 1) := by
  let u := Q.first.rectangle.specialD.extendBase Q.contains
  have h := u.inverse_contractible (u.toMap (Q.rightRESource p)) (u.toMap (Q.rightRESource q)) he
  rw [u.inverse_apply,u.inverse_apply] at h
  exact ((sameRV_iff _ _).mp h).1 0

def rightRFinalMap (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    Map Q.rightRSource (Q.rightTail N).target := Map.comp (Q.rightTail N).map Q.rightRToAmbient

theorem rightR_final_joint_kernel (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p q : Q.rightRSource) :
    (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N p)).val =
      (rawKeyMap (Q.rightTail N).target (Q.rightRFinalMap N q)).val ↔
        SameRV (Q.rightRDMap p).val (Q.rightRDMap q).val ∧ SameRV (Q.rightREMap p).val (Q.rightREMap q).val := by
  rw [rawKeyMap_eq_iff]
  rw [← unary_headKey_eq_iff_sameRV]
  exact lifted_unary_joint_kernel (Q.rightRectangleCompletion N).head.preparation.map
    (Q.rightRectangleCompletion N).head.preparation.special (Q.rightRectangleCompletion N).head.arity_le
    (Q.rightRectangleCompletion N).head.projection (Q.rightRectangleCompletion N).head.coverage
    (Q.rightRPreFinal N) Q.rightRDMap Q.rightREMap (fun p => vfAt p.val 1)
    (Q.rightRPreFinal_vf N) (Q.rightRPreFinal_kernel N) (Q.rightR_final_factor N) Q.rightRE_inverse_class p q

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
