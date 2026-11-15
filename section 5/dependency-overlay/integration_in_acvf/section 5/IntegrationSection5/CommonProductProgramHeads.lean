import IntegrationSection5.CommonProductInactive
import IntegrationSection5.RVSliceHeadImages
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
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}

theorem rvSlice_active_complement {n m : ℕ} {A : Set (Point (M := M) n m)}
    {E : Set (Fin m → RV (M := M))} {i : Fin n} {c : Point (M := M) n m → VF (M := M)}
    (U : RVSliceTranslationPreparation (G := G) A E i c) :
    carrier U.branch.target = {p | p ∈ carrier U.target ∧ p.2 ∘ Fin.natAdd 1 ∉ Eᶜ} := by
  rw [U.active_image]
  ext p
  exact and_congr_right (fun _ => not_not.symm)

namespace CanonicalProductBranchCompletion
variable {S : Set M} {n m b : ℕ} {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H : DefSet (M := M) S (n+1) (1+m)} {u : SpecialBijection A B} {E : Set (Fin m → RV (M := M))}
theorem preparation_boundary (C : CanonicalProductBranchCompletion (G := G) u H E) :
    SpecialRelativeBoundary C.preparation.map 0 (some true) (u.chain.lastKind C.start) :=
  specialRelativeBoundary_comp C.preMap C.head.preparation.map 0 C.prefix_special C.head.special
end CanonicalProductBranchCompletion

namespace PositionedCellLabelInjection.CommonProductHeadPair
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

def leftHead (P : CommonProductHeadPair T) : HeadPreparation (P.left.extendBase P.containsLeft).source where
  arity := P.completeLeft.preparation.arity
  target := P.completeLeft.preparation.target
  map := Map.comp P.completeLeft.preparation.map (P.left.extendBase P.containsLeft).map
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp (P.left.extendBase P.containsLeft).map
    P.completeLeft.preparation.map 0 (P.left.extendBase P.containsLeft).special P.completeLeft.preparation_boundary)
  saturated := P.completeLeft.preparation.saturated

def rightHead (P : CommonProductHeadPair T) : HeadPreparation (P.right.extendBase P.containsRight).source where
  arity := P.completeRight.preparation.arity
  target := P.completeRight.preparation.target
  map := Map.comp P.completeRight.preparation.map (P.right.extendBase P.containsRight).map
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp (P.right.extendBase P.containsRight).map
    P.completeRight.preparation.map 0 (P.right.extendBase P.containsRight).special P.completeRight.preparation_boundary)
  saturated := P.completeRight.preparation.saturated

theorem leftHead_gamma (P : CommonProductHeadPair T) : GammaGraphDefinable G (pointMapGraph P.leftHead.map) :=
  gamma_composition_graph (P.left.extendBase P.containsLeft).map P.completeLeft.preparation.map
    (P.left.extendBase P.containsLeft).graph P.completeLeft.graph

theorem rightHead_gamma (P : CommonProductHeadPair T) : GammaGraphDefinable G (pointMapGraph P.rightHead.map) :=
  gamma_composition_graph (P.right.extendBase P.containsRight).map P.completeRight.preparation.map
    (P.right.extendBase P.containsRight).graph P.completeRight.graph

def leftNImage (P : CommonProductHeadPair T) :=
  P.completeLeft.inactiveImage (rvSlice_active_complement (P.left.extendBase P.containsLeft))
def rightNImage (P : CommonProductHeadPair T) :=
  P.completeRight.inactiveImage (rvSlice_active_complement (P.right.extendBase P.containsRight))

def leftNPadding (P : CommonProductHeadPair T) :
    RVProjectionPadding (G := G) (headImage P.leftNImage)
      (headImage (P.left.extendBase P.containsLeft).branch.target)
      (headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special))) :=
  P.completeLeft.inactivePadding (rvSlice_active_complement (P.left.extendBase P.containsLeft)) P.left.branch.target_gamma

def rightNPadding (P : CommonProductHeadPair T) :
    RVProjectionPadding (G := G) (headImage P.rightNImage)
      (headImage (P.right.extendBase P.containsRight).branch.target)
      (headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special))) :=
  P.completeRight.inactivePadding (rvSlice_active_complement (P.right.extendBase P.containsRight)) P.right.branch.target_gamma

end PositionedCellLabelInjection.CommonProductHeadPair
end IntegrationInACVF.Section5
