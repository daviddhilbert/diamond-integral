import IntegrationSection3.Library
import IntegrationSection3.FieldLibrary
import IntegrationSection3.ProfileLibrary
import IntegrationSection3.CoordinateLibrary
import IntegrationSection2.Library
import IntegrationSection3ACVF.Library

/-! Checked source [18], sections 1–3, pinned at
7d4acc730496b3bd05a22c268ffd89540ca694f9. These are direct exports of the
upstream proofs, retaining their full original types and hypotheses.
Section 1 is introductory. Later integration/kernel results remain separate. -/
set_option autoImplicit false
namespace DiamondIntegral.Section3

abbrev integration_corollary_2_15 := @IntegrationInACVF.Section2.corollary_2_15
abbrev integration_corollary_2_34 := @IntegrationInACVF.Section2.corollary_2_34
abbrev integration_corollary_2_34_all_degrees :=
  @IntegrationInACVF.Section2.VolumeDescentAllDegrees.corollary_2_34_all_degrees
abbrev integration_lemma_3_2 := @IntegrationInACVF.Section3ACVF.FullBaseAtomicity.lemma_3_2
abbrev integration_lemma_3_3 := @IntegrationInACVF.Section3ACVF.FullGammaAtomicity.lemma_3_3
abbrev integration_lemma_3_4 := @IntegrationInACVF.Section3ACVF.CompleteTypeBallAtomicity.lemma_3_4
abbrev integration_lemma_3_6 := @IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.lemma_3_6
abbrev integration_corollary_3_7 := @IntegrationInACVF.Section3ACVF.SameRadiusCoverage.corollary_3_7_gamma
abbrev integration_lemma_3_8 := @IntegrationInACVF.Section3ACVF.PrimitiveImages.lemma_3_8
abbrev integration_lemma_3_9 := @IntegrationInACVF.Section3ACVF.OpenBallConstancy.lemma_3_9_open
abbrev integration_corollary_3_10 := @IntegrationInACVF.Section3ACVF.OpenBallConstancy.corollary_3_10_open
abbrev integration_lemma_3_11 := @IntegrationInACVF.Section3ACVF.Separation.lemma_3_11
abbrev integration_lemma_3_12_no_function :=
  @IntegrationInACVF.Section3ACVF.SeparationFunctions.no_function_from_open
abbrev integration_lemma_3_12_no_finite_to_one :=
  @IntegrationInACVF.Section3ACVF.SeparationFunctions.no_finite_to_one_to_open
abbrev integration_lemma_3_13 := @IntegrationInACVF.Section3ACVF.OpenImages.lemma_3_13
abbrev integration_lemma_3_14 := @IntegrationInACVF.Section3ACVF.ClosedImageObstruction.lemma_3_14
abbrev integration_lemma_3_15 := @IntegrationInACVF.Section3ACVF.FullCompleteTypeOpenImages.lemma_3_15
abbrev integration_lemma_3_16 := @IntegrationInACVF.Section3ACVF.GammaLinearity.lemma_3_16
abbrev integration_corollary_3_17_ordinary :=
  @IntegrationInACVF.Section3ACVF.LeastLinearRadiusExistence.corollary_3_17_ordinary
abbrev integration_corollary_3_17_conditional :=
  @IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.corollary_3_17
abbrev integration_lemma_3_18 := @IntegrationInACVF.Section3ACVF.RVLinearity.lemma_3_18
abbrev integration_proposition_3_19 := @IntegrationInACVF.Section3ACVF.FullOpenToOpenPartition.proposition_3_19
abbrev integration_proposition_3_21 := @IntegrationInACVF.Section3ACVF.CoordinatePartitions.proposition_3_21

abbrev integration_lemma_3_22 := @IntegrationInACVF.Section3ACVF.ThinFamilyConservation.lemma_3_22
abbrev integration_proposition_3_23 :=
  @IntegrationInACVF.Section3ACVF.AtomicPrimitiveDistinction.proposition_3_23
abbrev integration_proposition_3_24 :=
  @IntegrationInACVF.Section3ACVF.PuncturedBallObstruction.proposition_3_24

end DiamondIntegral.Section3
