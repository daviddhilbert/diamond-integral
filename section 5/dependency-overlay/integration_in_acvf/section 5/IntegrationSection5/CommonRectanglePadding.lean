import IntegrationSection5.SharedProductFirst
import IntegrationSection5.HeadProjectionFromFactor
import IntegrationSection5.CommonRectangleKernels
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

def leftRPadding (P : CommonProductHeadPair T)
    (F : SharedProductFirst (G := G) P.rectangle.source P.rectangle.sourceD P.rectangle.sourceE P.rectangle.targetD P.rectangle.specialD) :
    RVProjectionPadding (G := G) P.leftRHead.contractedSet F.preparation.contractedSet
      (factorHeadProjection P.completeLeft.head.projection F.projection F.projection_bijective) := by
  have hd : F.dSource = P.leftR_dSource := by
    apply Map.ext
    intro p
    apply Subtype.ext
    exact F.d_spec p
  have hFactor : ∀ p : P.rectangle.source, activeUnaryProjection 0 P.completeLeft.head.projection
      (P.leftRHead.map p).val = (P.rectangle.specialD.toMap (P.leftR_dSource p)).val := by
    intro p
    have h := P.completeLeft.head.square (P.leftR_preMap p) (P.leftR_preMap_flag p)
    have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (P.leftR_preMap p).val,
        P.completeLeft.head.embedding _ (P.leftR_preMap p).property (P.leftR_preMap_flag p)⟩ : P.rectangle.sourceD) = P.leftR_dSource p :=
      Subtype.ext (P.leftR_preMap_select p).symm
    rw [he] at h
    exact h
  have hF : ∀ p : P.rectangle.source, activeUnaryProjection 0 F.projection (F.preparation.map p).val =
      (P.rectangle.specialD.toMap (P.leftR_dSource p)).val := by
    intro p
    rw [← hd]
    exact F.square p
  refine headProjectionPaddingOfKernels P.leftRHead F.preparation P.completeLeft.head.projection
    F.projection F.projection_bijective (Map.comp P.rectangle.specialD.toMap P.leftR_dSource) hFactor hF ?_ ?_
    P.leftRHead_graph P.leftRHead_target_gamma F.graph F.target_gamma
  · intro p q
    rw [P.leftR_head_kernel]
    have h := surjective_head_factor_kernel F.preparation.map F.preparation.special F.projection
      F.projection_bijective.2 (Map.comp P.rectangle.specialD.toMap P.leftR_dSource) hF p q
    rw [Subtype.ext_iff]
    change _ ↔ (headKeyMap F.preparation.target (F.preparation.map p)).val =
      (headKeyMap F.preparation.target (F.preparation.map q)).val
    rw [headKeyMap_apply,headKeyMap_apply]
    exact h.symm
  · intro p q
    rw [P.leftR_head_sameRV_kernel]
    change _ ↔ SameRV (headKeyMap F.preparation.target (F.preparation.map p)).val
      (headKeyMap F.preparation.target (F.preparation.map q)).val
    rw [headKeyMap_apply,headKeyMap_apply]
    exact (surjective_head_factor_sameRV_kernel F.preparation.map F.preparation.special F.projection
      F.projection_bijective.2 (Map.comp P.rectangle.specialD.toMap P.leftR_dSource) hF p q).symm

def rightRPadding (P : CommonProductHeadPair T)
    (F : SharedProductFirst (G := G) P.rectangle.swap.source P.rectangle.sourceE P.rectangle.sourceD P.rectangle.targetE P.rectangle.specialE) :
    RVProjectionPadding (G := G) P.rightRHead.contractedSet F.preparation.contractedSet
      (factorHeadProjection P.completeRight.head.projection F.projection F.projection_bijective) := by
  have hd : F.dSource = P.rightR_dSource := by
    apply Map.ext
    intro p
    apply Subtype.ext
    exact F.d_spec p
  have hFactor : ∀ p : P.rectangle.swap.source, activeUnaryProjection 0 P.completeRight.head.projection
      (P.rightRHead.map p).val = (P.rectangle.specialE.toMap (P.rightR_dSource p)).val := by
    intro p
    have h := P.completeRight.head.square (P.rightR_preMap p) (P.rightR_preMap_flag p)
    have he : (⟨activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (P.rightR_preMap p).val,
        P.completeRight.head.embedding _ (P.rightR_preMap p).property (P.rightR_preMap_flag p)⟩ : P.rectangle.sourceE) = P.rightR_dSource p :=
      Subtype.ext (P.rightR_preMap_select p).symm
    rw [he] at h
    exact h
  have hF : ∀ p : P.rectangle.swap.source, activeUnaryProjection 0 F.projection (F.preparation.map p).val =
      (P.rectangle.specialE.toMap (P.rightR_dSource p)).val := by
    intro p
    rw [← hd]
    exact F.square p
  refine headProjectionPaddingOfKernels P.rightRHead F.preparation P.completeRight.head.projection
    F.projection F.projection_bijective (Map.comp P.rectangle.specialE.toMap P.rightR_dSource) hFactor hF ?_ ?_
    P.rightRHead_graph P.rightRHead_target_gamma F.graph F.target_gamma
  · intro p q
    rw [P.rightR_head_kernel]
    have h := surjective_head_factor_kernel F.preparation.map F.preparation.special F.projection
      F.projection_bijective.2 (Map.comp P.rectangle.specialE.toMap P.rightR_dSource) hF p q
    rw [Subtype.ext_iff]
    change _ ↔ (headKeyMap F.preparation.target (F.preparation.map p)).val =
      (headKeyMap F.preparation.target (F.preparation.map q)).val
    rw [headKeyMap_apply,headKeyMap_apply]
    exact h.symm
  · intro p q
    rw [P.rightR_head_sameRV_kernel]
    change _ ↔ SameRV (headKeyMap F.preparation.target (F.preparation.map p)).val
      (headKeyMap F.preparation.target (F.preparation.map q)).val
    rw [headKeyMap_apply,headKeyMap_apply]
    exact (surjective_head_factor_sameRV_kernel F.preparation.map F.preparation.special F.projection
      F.projection_bijective.2 (Map.comp P.rectangle.specialE.toMap P.rightR_dSource) hF p q).symm

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
