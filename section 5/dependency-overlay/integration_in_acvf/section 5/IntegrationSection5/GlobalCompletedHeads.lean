import IntegrationSection5.RVSliceHeadCompletion
import IntegrationSection5.MixedUnaryPreparationOver
import IntegrationSection5.TranslationExtension
import IntegrationSection5.InactiveRectangleFamily
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {E : Set (Fin m → RV (M := M))}
variable {c : Point (M := M) 2 m → VF (M := M)}

namespace PositionedCellLabelInjection
variable {X : Set (Point (M := M) 2 m)}
theorem global_completed_head_preparations {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G X) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1),
      (∀ p, (e.equiv p).val.2 = p.val.2) ∧
      (∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) ∧
      ∃ L : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre e),
        HeadSaturated (carrier L.branch.target) ∧ Nonempty (RVSliceHeadCompletion L) ∧
        ∃ R : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre e),
          HeadSaturated (carrier R.branch.target) ∧ Nonempty (RVSliceHeadCompletion R) := by
  obtain ⟨e,hLabels,hSpec,L,hL,R,hR⟩ := T.global_nonrectangle_head_preparations δ hδ
  obtain ⟨CL⟩ := rv_slice_head_completion hs h00 hsmall F L hL
    (T.horizontal_inactive_gamma L) (T.horizontal_inactive_rectangles L)
  obtain ⟨CR⟩ := rv_slice_head_completion hs h00 hsmall F R hR
    (T.vertical_inactive_gamma R) (T.vertical_inactive_rectangles R)
  exact ⟨e,hLabels,hSpec,L,hL,⟨CL⟩,R,hR,⟨CR⟩⟩
end PositionedCellLabelInjection
end IntegrationInACVF.Section5
