import IntegrationSection5.FinalRawPartition
import IntegrationSection5.FinalNProgramProfiles
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
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def full_native_profile_comparison (Z : CommonProductNComparison T δ hδ) :
    GammaRVIso G (Z.matching.leftWholeProfile Z.left) (Z.matching.rightWholeProfile Z.right) := by
  let Q := Z.matching
  refine gammaRVPartitionIso (Q.leftWholeProfile Z.left) (Q.rightWholeProfile Z.right)
    (Q.leftNRawDomain Z.left) (Q.leftRRawDomain Z.left) (Q.rightNRawDomain Z.right) (Q.rightRRawDomain Z.right)
    (Q.leftNRaw_sub Z.left) (Q.leftRRaw_sub Z.left) (Q.rightNRaw_sub Z.right) (Q.rightRRaw_sub Z.right)
    (Q.leftRaw_disjoint Z.left) (Q.rightRaw_disjoint Z.right) (Q.leftRaw_cover Z.left) (Q.rightRaw_cover Z.right)
    (Q.leftWholeProfile_gamma Z.left) (Q.rightWholeProfile_gamma Z.right) ?_ ?_
  · change GammaRVIso G
      (@SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) Q.unary.codes 2
        (selectedVolumeObject (Q.leftWholeRawDomain Z.left) (Q.leftProgram Z.left).volumeIndex) (Q.leftNRawDomain Z.left) _)
      (@SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) Q.unary.codes 2
        (selectedVolumeObject (Q.rightWholeRawDomain Z.right) (Q.rightProgram Z.right).volumeIndex) (Q.rightNRawDomain Z.right) _)
    rw [selectedVolumeObject_restrict,selectedVolumeObject_restrict]
    exact Z.final_nonrectangle_program_profiles
  · change GammaRVIso G
      (@SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) Q.unary.codes 2
        (selectedVolumeObject (Q.leftWholeRawDomain Z.left) (Q.leftProgram Z.left).volumeIndex) (Q.leftRRawDomain Z.left) _)
      (@SpecialTransformations.Section4.RVObject.restrict M (@CanonicalStructure.normalize M sM) Q.unary.codes 2
        (selectedVolumeObject (Q.rightWholeRawDomain Z.right) (Q.rightProgram Z.right).volumeIndex) (Q.rightRRawDomain Z.right) _)
    rw [selectedVolumeObject_restrict,selectedVolumeObject_restrict]
    exact Z.final_rectangle_profile_comparison

def full_native_program_comparison (Z : CommonProductNComparison T δ hδ) :
    GammaRVIso G (Z.matching.leftProgram Z.left).contractionObject (Z.matching.rightProgram Z.right).contractionObject :=
  (gammaUnaryHeadVolumeIso (Z.matching.leftTail Z.left).target (Z.matching.leftTail_target_gamma Z.left)
    (Z.matching.leftProgram Z.left).volumeIndex).trans
      (Z.full_native_profile_comparison.trans
        (gammaUnaryHeadVolumeIso (Z.matching.rightTail Z.right).target (Z.matching.rightTail_target_gamma Z.right)
          (Z.matching.rightProgram Z.right).volumeIndex).symm)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
