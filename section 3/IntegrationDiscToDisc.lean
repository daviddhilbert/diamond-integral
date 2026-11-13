import «section 3».IntegrationDiscPartition
set_option autoImplicit false
/-! The former disc-to-disc cited input is supplied by the checked mixed
partition [18, 3.21], with a native finite-radius zero-cell refinement. -/
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integrationDiscToDiscPartitionInput {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : GammaParameters.Base (M := M)) :
    Section2.DiscToDiscPartitionInput B := by
  intro h00 hΓ r s A C f _ _ hf hbij
  exact integrationDiscToDiscPartition hκ hs B h00 hΓ A f hf hbij.injOn

theorem integration_lemma_2_32 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (E : Section2.ParameterBase M) (hΓ : Section2.NontrivialDefinableGamma E)
    {r s : ℕ} (A : Set (Section2.Mixed M 1 r)) (B : Set (Section2.Mixed M 1 s))
    (f : Section2.Mixed M 1 r → Section2.Mixed M 1 s)
    (hA : Section2.MixedDefinable E A) (hB : Section2.MixedDefinable E B)
    (hf : Section2.MixedMapDefinable E A f) (hbij : Set.BijOn f A B) :
    Section2.DiscToDiscPartition E A f :=
  Section2.lemma_2_32 h00 E (integrationDiscToDiscPartitionInput hκ hs E) hΓ A B f hA hB hf hbij
end DiamondIntegral.Section3
