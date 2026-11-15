import IntegrationSection5.CommonRectangleHead
import IntegrationSection5.MixedUnaryPreparationSwap
import IntegrationSection5.InactiveRectangleFamily
import IntegrationSection5.MixedUnaryPreparationOver
import IntegrationSection5.NonrectangleHeadRVClasses
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
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)}
open SpecialTransformations.Section3

structure CommonProductHeadPair (T : PositionedCellLabelInjection G A) where
  position : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
    (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)
  labels : ∀ p, (position.equiv p).val.2 = p.val.2
  spec : ∀ p, vfAt (position.equiv p).val 0 = T.nonrectanglePosition p
  left : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre position)
  left_sat : HeadSaturated (carrier left.branch.target)
  right : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre position)
  right_sat : HeadSaturated (carrier right.branch.target)
  rectangle : MixedUnaryPreparations (G := G) (rectangleFamilyBranch T.target)
  containsLeft : left.branch.codes ⊆ rectangle.codes
  containsRight : right.branch.codes ⊆ rectangle.codes
  completeLeft : CanonicalProductBranchCompletion (G := G) rectangle.specialD
    (left.extendBase containsLeft).target T.nonrectangleRVLabelsᶜ
  completeRight : CanonicalProductBranchCompletion (G := G) rectangle.specialE
    (right.extendBase containsRight).target T.nonrectangleRVLabelsᶜ

theorem common_product_head_pair {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    Nonempty (CommonProductHeadPair T) := by
  obtain ⟨e,hLabels,hSpec,L,hL,R,hR⟩ := T.global_nonrectangle_head_preparations δ hδ
  obtain ⟨P,hP⟩ := mixed_unary_preparations_over hs h00 hsmall F (L.branch.codes ∪ R.branch.codes)
    (rectangleFamilyBranch T.target) (rectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G)))
  have hLP : L.branch.codes ⊆ P.codes := fun _ hx => hP (Or.inl hx)
  have hRP : R.branch.codes ⊆ P.codes := fun _ hx => hP (Or.inr hx)
  have hClassL : ∀ p ∈ carrier P.sourceD, ∀ q ∈ carrier P.sourceD,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq he
    exact mixed_projection_rvclass (rectangleFamilyBranch T.target) 0
      (fun a ha b hb hl => (T.same_labels_same_vf_rv a b ha.1 hb.1 hl).1)
      ⟨p,(Set.ext_iff.mp P.sourceD_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp P.sourceD_eq q).mp hq⟩ he
  have hClassR : ∀ p ∈ carrier P.sourceE, ∀ q ∈ carrier P.sourceE,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq he
    exact mixed_projection_rvclass (rectangleFamilyBranch T.target) 1
      (fun a ha b hb hl => (T.same_labels_same_vf_rv a b ha.1 hb.1 hl).2)
      ⟨p,(Set.ext_iff.mp P.sourceE_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp P.sourceE_eq q).mp hq⟩ he
  obtain ⟨CL⟩ := rv_slice_common_product_head L hL P hLP (rectangleFamilyBranch_rectangles T.target) hClassL
  obtain ⟨CR⟩ := rv_slice_common_product_head R hR P.swap hRP
    (rvFibreRectangles_vfSwap _ (rectangleFamilyBranch_rectangles T.target)) hClassR
  exact ⟨⟨e,hLabels,hSpec,L,hL,R,hR,P,hLP,hRP,CL,CR⟩⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
