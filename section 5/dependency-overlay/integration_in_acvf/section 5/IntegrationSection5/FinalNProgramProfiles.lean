import IntegrationSection5.FinalNIndices
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def final_nonrectangle_program_profiles (Z : CommonProductNComparison T δ hδ) :
    GammaRVIso G
      (selectedVolumeObject (Map.image (rawKeyMap (Z.matching.leftNFinalImage Z.left)))
        (Z.matching.leftProgram Z.left).volumeIndex)
      (selectedVolumeObject (Map.image (rawKeyMap (Z.matching.rightNFinalImage Z.right)))
        (Z.matching.rightProgram Z.right).volumeIndex) := by
  rw [← Z.matching.leftNFinalIndices Z.left,← Z.matching.rightNFinalIndices Z.right]
  exact Z.final_nonrectangle_profile_comparison

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductNComparison
