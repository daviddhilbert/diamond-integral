import IntegrationSection5.CompletedNonrectangleMatching
import IntegrationSection5.CanonicalUnaryBranchExtension
import IntegrationSection5.UnarySpecialRelative
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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n a b : ℕ}

theorem gamma_specialCastBoth {A A' : DefSet (M := M) S n a} {B B' : DefSet (M := M) S n b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain) (hA : A = A') (hB : B = B') :
    GammaChainDefinable G (specialCastBoth T hA hB).chain := by
  subst A'; subst B'; exact hT

namespace PositionedCellLabelInjection.CompletedNonrectangleMatching
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def containsLeft (Q : CompletedNonrectangleMatching T δ hδ) : Q.heads.completeLeft.rectangle.codes ⊆ Q.unary.codes :=
  fun _ hx => Q.contains (Or.inl hx)
def containsRight (Q : CompletedNonrectangleMatching T δ hδ) : Q.heads.completeRight.rectangle.codes ⊆ Q.unary.codes :=
  fun _ hx => Q.contains (Or.inr hx)

def branchA (Q : CompletedNonrectangleMatching T δ hδ) := extendBase Q.heads.sourceA Q.containsLeft
def branchB (Q : CompletedNonrectangleMatching T δ hδ) := extendBase Q.heads.sourceB Q.containsRight
def ambientA (Q : CompletedNonrectangleMatching T δ hδ) :=
  extendBase Q.heads.completeLeft.preparation.contractedSet Q.containsLeft
def ambientB (Q : CompletedNonrectangleMatching T δ hδ) :=
  extendBase Q.heads.completeRight.preparation.contractedSet Q.containsRight

def labelsA (Q : CompletedNonrectangleMatching T δ hδ) :=
  {s | s ∘ Q.heads.completeLeft.originalLabelIndex ∈ T.nonrectangleRVLabels}
def labelsB (Q : CompletedNonrectangleMatching T δ hδ) :=
  {s | s ∘ Q.heads.completeRight.originalLabelIndex ∈ T.nonrectangleRVLabels}

theorem branchA_slice (Q : CompletedNonrectangleMatching T δ hδ) :
    carrier Q.branchA = {p | p ∈ carrier Q.ambientA ∧ p.2 ∈ Q.labelsA} :=
  Q.heads.completeLeft.nonrectangle_head_slice

theorem branchB_slice (Q : CompletedNonrectangleMatching T δ hδ) :
    carrier Q.branchB = {p | p ∈ carrier Q.ambientB ∧ p.2 ∈ Q.labelsB} :=
  Q.heads.completeRight.nonrectangle_head_slice

theorem unaryA_source (Q : CompletedNonrectangleMatching T δ hδ) :
    Q.unary.sourceA = coordinateCanonicalImage Q.branchA 0 :=
  PresentedSet.eq_of_carrier_eq Q.unary.sourceA_eq

theorem unaryB_source (Q : CompletedNonrectangleMatching T δ hδ) :
    Q.unary.sourceB = coordinateCanonicalImage Q.branchB 0 :=
  PresentedSet.eq_of_carrier_eq Q.unary.sourceB_eq

def specialA (Q : CompletedNonrectangleMatching T δ hδ) :
    SpecialBijection (coordinateCanonicalImage Q.branchA 0) Q.unary.targetA :=
  specialCastBoth Q.unary.specialA Q.unaryA_source rfl

def specialB (Q : CompletedNonrectangleMatching T δ hδ) :
    SpecialBijection (coordinateCanonicalImage Q.branchB 0) Q.unary.targetB :=
  specialCastBoth Q.unary.specialB Q.unaryB_source rfl

theorem specialA_gamma (Q : CompletedNonrectangleMatching T δ hδ) : GammaChainDefinable G Q.specialA.chain :=
  gamma_specialCastBoth Q.unary.specialA Q.unary.gammaA Q.unaryA_source rfl

theorem specialB_gamma (Q : CompletedNonrectangleMatching T δ hδ) : GammaChainDefinable G Q.specialB.chain :=
  gamma_specialCastBoth Q.unary.specialB Q.unary.gammaB Q.unaryB_source rfl

theorem left_extension (Q : CompletedNonrectangleMatching T δ hδ) :
    Nonempty (CanonicalUnaryBranchExtension (G := G) Q.specialA Q.ambientA Q.labelsA none) :=
  canonical_unary_branch_extension Q.specialA Q.specialA_gamma Q.unary.pullbackA
    (gamma_headImage Q.heads.completeLeft.preparation.target Q.heads.completeLeft.preparation_target_gamma)
    (((Q.heads.iso δ hδ).symm (gammaLogicInput G)).target_definable (gammaLogicInput G))
    Q.labelsA Q.branchA_slice none (fun h => by cases h)

theorem right_extension (Q : CompletedNonrectangleMatching T δ hδ) :
    Nonempty (CanonicalUnaryBranchExtension (G := G) Q.specialB Q.ambientB Q.labelsB none) :=
  canonical_unary_branch_extension Q.specialB Q.specialB_gamma Q.unary.pullbackB
    (gamma_headImage Q.heads.completeRight.preparation.target Q.heads.completeRight.preparation_target_gamma)
    ((Q.heads.iso δ hδ).target_definable (gammaLogicInput G))
    Q.labelsB Q.branchB_slice none (fun h => by cases h)

end PositionedCellLabelInjection.CompletedNonrectangleMatching
end IntegrationInACVF.Section5
