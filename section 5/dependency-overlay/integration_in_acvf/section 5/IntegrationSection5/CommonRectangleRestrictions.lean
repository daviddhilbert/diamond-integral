import IntegrationSection5.CommonProductProgramHeads
import IntegrationSection5.RVSliceHeadRestriction
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

theorem leftHead_boundary (P : CommonProductHeadPair T) :
    SpecialRelativeBoundary P.leftHead.map 0 none (P.rectangle.specialD.chain.lastKind P.completeLeft.start) :=
  specialRelativeBoundary_comp (P.left.extendBase P.containsLeft).map P.completeLeft.preparation.map 0
    (P.left.extendBase P.containsLeft).special P.completeLeft.preparation_boundary

theorem rightHead_boundary (P : CommonProductHeadPair T) :
    SpecialRelativeBoundary P.rightHead.map 0 none (P.rectangle.specialE.chain.lastKind P.completeRight.start) :=
  specialRelativeBoundary_comp (P.right.extendBase P.containsRight).map P.completeRight.preparation.map 0
    (P.right.extendBase P.containsRight).special P.completeRight.preparation_boundary

theorem leftR_source (P : CommonProductHeadPair T) : carrier P.rectangle.source =
    {p | p ∈ carrier (P.left.extendBase P.containsLeft).source ∧ p.2 ∈ T.nonrectangleRVLabelsᶜ} := by
  change carrier P.rectangle.source = {p | p ∈ carrier P.left.source ∧ p.2 ∈ T.nonrectangleRVLabelsᶜ}
  rw [P.rectangle.source_eq,P.left.source_eq]
  rfl

theorem rightR_source (P : CommonProductHeadPair T) : carrier P.rectangle.swap.source =
    {p | p ∈ carrier (P.right.extendBase P.containsRight).source ∧ p.2 ∈ T.nonrectangleRVLabelsᶜ} := by
  change carrier P.rectangle.swap.source = {p | p ∈ carrier P.right.source ∧ p.2 ∈ T.nonrectangleRVLabelsᶜ}
  rw [P.rectangle.swap.source_eq,P.right.source_eq]
  rfl

def leftRHead (P : CommonProductHeadPair T) : HeadPreparation P.rectangle.source :=
  P.leftHead.rvSliceRestriction T.nonrectangleRVLabelsᶜ P.leftR_source P.leftHead_boundary

def rightRHead (P : CommonProductHeadPair T) : HeadPreparation P.rectangle.swap.source :=
  P.rightHead.rvSliceRestriction T.nonrectangleRVLabelsᶜ P.rightR_source P.rightHead_boundary

theorem leftR_gamma (P : CommonProductHeadPair T) : GammaSetDefinable G (carrier P.rectangle.source) :=
  P.rectangle.source_eq.symm ▸ rectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G))

theorem rightR_gamma (P : CommonProductHeadPair T) : GammaSetDefinable G (carrier P.rectangle.swap.source) :=
  P.rectangle.swap.source_eq.symm ▸ gamma_mixedVFSelect_preimage (Equiv.swap 0 1) _
    (rectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G)))

theorem leftRHead_graph (P : CommonProductHeadPair T) : GammaGraphDefinable G (pointMapGraph P.leftRHead.map) :=
  P.leftHead.rvSliceRestriction_gamma T.nonrectangleRVLabelsᶜ P.leftR_source P.leftHead_boundary P.leftR_gamma P.leftHead_gamma

theorem rightRHead_graph (P : CommonProductHeadPair T) : GammaGraphDefinable G (pointMapGraph P.rightRHead.map) :=
  P.rightHead.rvSliceRestriction_gamma T.nonrectangleRVLabelsᶜ P.rightR_source P.rightHead_boundary P.rightR_gamma P.rightHead_gamma

theorem leftRHead_target_gamma (P : CommonProductHeadPair T) : GammaSetDefinable G (carrier P.leftRHead.target) :=
  P.leftHead.rvSliceRestriction_target_gamma T.nonrectangleRVLabelsᶜ P.leftR_source P.leftHead_boundary P.leftR_gamma P.leftHead_gamma

theorem rightRHead_target_gamma (P : CommonProductHeadPair T) : GammaSetDefinable G (carrier P.rightRHead.target) :=
  P.rightHead.rvSliceRestriction_target_gamma T.nonrectangleRVLabelsᶜ P.rightR_source P.rightHead_boundary P.rightR_gamma P.rightHead_gamma

def leftR_preMap (P : CommonProductHeadPair T) : Map P.rectangle.source P.completeLeft.prefixTarget :=
  Map.comp P.completeLeft.preMap (Map.comp (P.left.extendBase P.containsLeft).map
    (Map.inclusion (P.leftHead.rvSliceSubset T.nonrectangleRVLabelsᶜ P.leftR_source)))

def rightR_preMap (P : CommonProductHeadPair T) : Map P.rectangle.swap.source P.completeRight.prefixTarget :=
  Map.comp P.completeRight.preMap (Map.comp (P.right.extendBase P.containsRight).map
    (Map.inclusion (P.rightHead.rvSliceSubset T.nonrectangleRVLabelsᶜ P.rightR_source)))

theorem leftR_preMap_formula (P : CommonProductHeadPair T) (p : P.rectangle.source) :
    (P.leftR_preMap p).val = coordinateCanonical 0 (coordinateCanonical 0 p.val) := by
  have hOff : p.val.2 ∉ T.nonrectangleRVLabels := ((Set.ext_iff.mp P.leftR_source p.val).mp p.property).2
  let a : (P.left.extendBase P.containsLeft).source :=
    ⟨p.val,P.leftHead.rvSliceSubset T.nonrectangleRVLabelsᶜ P.leftR_source p.property⟩
  have hA := (P.left.extendBase P.containsLeft).formula a
  rw [if_neg hOff] at hA
  exact (P.completeLeft.prefix_formula ((P.left.extendBase P.containsLeft).map a)).trans (congrArg (coordinateCanonical 0) hA)

theorem rightR_preMap_formula (P : CommonProductHeadPair T) (p : P.rectangle.swap.source) :
    (P.rightR_preMap p).val = coordinateCanonical 0 (coordinateCanonical 0 p.val) := by
  have hOff : p.val.2 ∉ T.nonrectangleRVLabels := ((Set.ext_iff.mp P.rightR_source p.val).mp p.property).2
  let a : (P.right.extendBase P.containsRight).source :=
    ⟨p.val,P.rightHead.rvSliceSubset T.nonrectangleRVLabelsᶜ P.rightR_source p.property⟩
  have hA := (P.right.extendBase P.containsRight).formula a
  rw [if_neg hOff] at hA
  exact (P.completeRight.prefix_formula ((P.right.extendBase P.containsRight).map a)).trans (congrArg (coordinateCanonical 0) hA)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
