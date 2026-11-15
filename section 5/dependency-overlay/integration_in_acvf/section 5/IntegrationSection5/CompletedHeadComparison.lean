import IntegrationSection5.CompletedNonrectangleHead
import IntegrationSection5.InactiveBranchHeadIso
import IntegrationSection5.RVSliceHeadImages
import IntegrationSection5.NonrectangleHeadPresentations
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
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)}

def nonrectanglePresentationsOfStages (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (L : CanonicalTranslationPreparation (G := G) (nonrectangleFamilyBranch T.target) 0 (T.horizontalCentre e))
    (hL : HeadSaturated (carrier L.target))
    (R : CanonicalTranslationPreparation (G := G) T.swappedNonrectangleFamily 0 (T.verticalCentre e))
    (hR : HeadSaturated (carrier R.target)) : NonrectangleHeadPresentations T := by
  let hResL := fun p hp q hq hl => T.horizontalCentre_residual_same_labels δ hδ e hLabels hSpec p q hp hq hl
  let hOldL : ∀ p ∈ nonrectangleFamilyBranch T.target, ∀ q ∈ nonrectangleFamilyBranch T.target,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) :=
    fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1
  let PL := mixedStripPassiveIso L hL hResL hOldL
  have hOldR : ∀ p ∈ T.swappedNonrectangleFamily, ∀ q ∈ T.swappedNonrectangleFamily,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq hl
    have h := (T.same_labels_same_vf_rv (vfPermutation (Equiv.swap 0 1) p)
      (vfPermutation (Equiv.swap 0 1) q) hp.1 hq.1 hl).2
    simpa only [vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right] using h
  let hResR := fun p hp q hq hl => T.verticalCentre_residual_same_labels δ hδ e hSpec p q hp hq hl
  let PR := gammaIsoCastTarget (mixedStripPassiveIso R hR hResR hOldR) T.swappedNonrectangle_passive_projection
  refine ⟨e,hLabels,hSpec,L,hL,R,hR,PL,?_,PR,?_⟩
  · exact mixedStripPassiveIso_apply L hL hResL hOldL
  · intro a
    exact (gammaIsoCastTarget_apply _ _ a).trans (mixedStripPassiveIso_apply R hR hResR hOldR a)

def completedNonrectangleHeadIso (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ p, (e.equiv p).val.2 = p.val.2)
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (L : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre e))
    (hL : HeadSaturated (carrier L.branch.target))
    (R : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre e))
    (hR : HeadSaturated (carrier R.branch.target))
    (CL : RVSliceHeadCompletion L) (CR : RVSliceHeadCompletion R) :
    GammaIso G (carrier (headImage CL.nonrectangleImage)) (carrier (headImage CR.nonrectangleImage)) :=
  ((CL.nonrectangleHeadIso.symm (gammaLogicInput G)).trans (gammaLogicInput G)
    (T.nonrectanglePresentationsOfStages δ hδ e hLabels hSpec L.branch hL R.branch hR).headIso).trans
      (gammaLogicInput G) CR.nonrectangleHeadIso

end IntegrationInACVF.Section5.PositionedCellLabelInjection
