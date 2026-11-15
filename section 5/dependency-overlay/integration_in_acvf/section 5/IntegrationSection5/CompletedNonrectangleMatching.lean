import IntegrationSection5.CompletedHeadComparison
import IntegrationSection5.GlobalCompletedHeads
import IntegrationSection5.MatchedUnaryPreparation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

structure CompletedHeadPair (T : PositionedCellLabelInjection G A) where
  position : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
    (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)
  labels : ∀ p, (position.equiv p).val.2 = p.val.2
  spec : ∀ p, vfAt (position.equiv p).val 0 = T.nonrectanglePosition p
  left : RVSliceTranslationPreparation (G := G) T.target T.nonrectangleRVLabels 0 (T.horizontalCentre position)
  left_sat : HeadSaturated (carrier left.branch.target)
  right : RVSliceTranslationPreparation (G := G) T.swappedTarget T.nonrectangleRVLabels 0 (T.verticalCentre position)
  right_sat : HeadSaturated (carrier right.branch.target)
  completeLeft : RVSliceHeadCompletion left
  completeRight : RVSliceHeadCompletion right

namespace CompletedHeadPair
variable {T : PositionedCellLabelInjection G A}
def sourceA (P : CompletedHeadPair T) := headImage P.completeLeft.nonrectangleImage
def sourceB (P : CompletedHeadPair T) := headImage P.completeRight.nonrectangleImage

def iso (P : CompletedHeadPair T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    GammaIso G (carrier P.sourceA) (carrier P.sourceB) :=
  T.completedNonrectangleHeadIso δ hδ P.position P.labels P.spec P.left P.left_sat P.right P.right_sat
    P.completeLeft P.completeRight

def canonicalIso (P : CompletedHeadPair T) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    GammaIso G (carrier (coordinateCanonicalImage P.sourceA 0)) (carrier (coordinateCanonicalImage P.sourceB 0)) :=
  (((coordinateCanonicalGammaIso P.sourceA (((P.iso δ hδ).symm (gammaLogicInput G)).target_definable (gammaLogicInput G)) 0).symm
    (gammaLogicInput G)).trans (gammaLogicInput G) (P.iso δ hδ)).trans (gammaLogicInput G)
      (coordinateCanonicalGammaIso P.sourceB ((P.iso δ hδ).target_definable (gammaLogicInput G)) 0)
end CompletedHeadPair

theorem completed_head_pair {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    Nonempty (CompletedHeadPair T) := by
  obtain ⟨e,hLabels,hSpec,L,hL,⟨CL⟩,R,hR,⟨CR⟩⟩ := T.global_completed_head_preparations hs h00 hsmall F δ hδ
  exact ⟨⟨e,hLabels,hSpec,L,hL,R,hR,CL,CR⟩⟩

structure CompletedNonrectangleMatching (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) where
  heads : CompletedHeadPair T
  unary : MatchedUnaryPreparation (G := G)
    (carrier (coordinateCanonicalImage heads.sourceA 0)) (carrier (coordinateCanonicalImage heads.sourceB 0))
    (heads.canonicalIso δ hδ).equiv
  contains : heads.completeLeft.rectangle.codes ∪ heads.completeRight.rectangle.codes ⊆ unary.codes

theorem completed_nonrectangle_matching {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (T : PositionedCellLabelInjection G A) : Nonempty (CompletedNonrectangleMatching T δ hδ1) := by
  obtain ⟨P⟩ := T.completed_head_pair hs h00 hsmall F δ hδ1
  let e := P.canonicalIso δ hδ1
  obtain ⟨Q,hQ⟩ := matched_unary_preparation_over hκ hs hsmall h00 δ hδ hδ1 F
    (P.completeLeft.rectangle.codes ∪ P.completeRight.rectangle.codes) _ _
      ((e.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)) (e.target_definable (gammaLogicInput G)) e
  exact ⟨⟨P,Q,hQ⟩⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
