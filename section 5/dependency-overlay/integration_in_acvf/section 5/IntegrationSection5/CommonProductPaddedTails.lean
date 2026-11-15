import IntegrationSection5.CommonProductMatching
import IntegrationSection5.CommonProductHeadSlices
import IntegrationSection5.ProjectionPaddingOperations
import IntegrationSection5.PaddedUnaryBranchExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A} {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def leftBranch (Q : CommonProductMatching T δ hδ) := extendBase (headImage Q.first.leftNImage) Q.contains
def rightBranch (Q : CommonProductMatching T δ hδ) := extendBase (headImage Q.first.rightNImage) Q.contains
def leftAmbient (Q : CommonProductMatching T δ hδ) := extendBase Q.first.leftHead.contractedSet Q.contains
def rightAmbient (Q : CommonProductMatching T δ hδ) := extendBase Q.first.rightHead.contractedSet Q.contains

def leftProjection (Q : CommonProductMatching T δ hδ) :=
  headPaddingProjection (suffixIndex (specialRelative_rvArity_le Q.first.completeLeft.preparation.special))
def rightProjection (Q : CommonProductMatching T δ hδ) :=
  headPaddingProjection (suffixIndex (specialRelative_rvArity_le Q.first.completeRight.preparation.special))

def oldNLabels : Set (Fin (1+(1+T.arity)) → RV (M := M)) := {s | s ∘ stripPassiveIndex T.arity ∈ T.nonrectangleRVLabels}

def leftPadding (Q : CommonProductMatching T δ hδ) : RVProjectionPadding (G := G) Q.leftBranch Q.unary.sourceA Q.leftProjection :=
  (Q.first.leftNPadding.extendBase Q.contains).castTarget (PresentedSet.eq_of_carrier_eq Q.unary.sourceA_eq.symm)
def rightPadding (Q : CommonProductMatching T δ hδ) : RVProjectionPadding (G := G) Q.rightBranch Q.unary.sourceB Q.rightProjection :=
  (Q.first.rightNPadding.extendBase Q.contains).castTarget (PresentedSet.eq_of_carrier_eq Q.unary.sourceB_eq.symm)

theorem left_source_slice (Q : CommonProductMatching T δ hδ) :
    carrier Q.leftBranch = {p | p ∈ carrier Q.leftAmbient ∧ p.2 ∘ Q.leftProjection ∈ oldNLabels (T := T)} :=
  Q.first.leftN_slice

theorem right_source_slice (Q : CommonProductMatching T δ hδ) :
    carrier Q.rightBranch = {p | p ∈ carrier Q.rightAmbient ∧ p.2 ∘ Q.rightProjection ∈ oldNLabels (T := T)} :=
  Q.first.rightN_slice

theorem left_source_class (Q : CommonProductMatching T δ hδ) :
    ∀ p ∈ carrier Q.unary.sourceA, ∀ q ∈ carrier Q.unary.sourceA,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
  intro p hp q hq he
  exact Q.asOld.first.left_rvclass_same_labels
    ⟨p,(Set.ext_iff.mp Q.unary.sourceA_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp Q.unary.sourceA_eq q).mp hq⟩ he

theorem right_source_class (Q : CommonProductMatching T δ hδ) :
    ∀ p ∈ carrier Q.unary.sourceB, ∀ q ∈ carrier Q.unary.sourceB,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
  intro p hp q hq he
  exact Q.asOld.first.right_rvclass_same_labels
    ⟨p,(Set.ext_iff.mp Q.unary.sourceB_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp Q.unary.sourceB_eq q).mp hq⟩ he

theorem left_padded_tail (Q : CommonProductMatching T δ hδ) :
    Nonempty (PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  padded_unary_branch_extension Q.unary.specialA Q.unary.gammaA Q.unary.pullbackA
    (gamma_headImage Q.first.leftHead.target Q.first.completeLeft.head.target_gamma)
    Q.leftProjection (oldNLabels (T := T)) Q.left_source_slice Q.leftPadding Q.left_source_class none (fun h => by cases h)

theorem right_padded_tail (Q : CommonProductMatching T δ hδ) :
    Nonempty (PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  padded_unary_branch_extension Q.unary.specialB Q.unary.gammaB Q.unary.pullbackB
    (gamma_headImage Q.first.rightHead.target Q.first.completeRight.head.target_gamma)
    Q.rightProjection (oldNLabels (T := T)) Q.right_source_slice Q.rightPadding Q.right_source_class none (fun h => by cases h)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
