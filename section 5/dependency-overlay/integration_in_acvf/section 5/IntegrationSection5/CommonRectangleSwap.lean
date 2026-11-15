import IntegrationSection5.CommonRectangleRaw
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

def rectangleSwap (Q : CommonProductMatching T δ hδ) : Map Q.leftRSource Q.rightRSource :=
  vfPermutationBijection Q.leftRSource (Equiv.swap 0 1)

theorem rectangleSwap_bijective (Q : CommonProductMatching T δ hδ) : Function.Bijective Q.rectangleSwap :=
  vfPermutationBijection_bijective Q.leftRSource (Equiv.swap 0 1)

theorem rectangleSwap_graph (Q : CommonProductMatching T δ hδ) :
    GammaGraphDefinable G (pointMapGraph Q.rectangleSwap) :=
  gamma_vfPermutation_graph Q.leftRSource Q.first.leftR_gamma (Equiv.swap 0 1)

theorem rightRDMap_swap (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    Q.rightRDMap (Q.rectangleSwap p) = Q.leftREMap p := by
  apply Subtype.ext
  exact (Q.first.rectangle.specialE.chain.extendBase_apply Q.contains (Q.leftRESource p)).symm

theorem rightREMap_swap (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    Q.rightREMap (Q.rectangleSwap p) = Q.leftRDMap p := by
  apply Subtype.ext
  exact Q.first.rectangle.specialD.chain.extendBase_apply Q.contains (Q.rightRESource (Q.rectangleSwap p))

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
