import «section 3».UnmeasuredTensorChart
import «section 3».CompletionSurjectivity
import «section 3».PositivePresentationSurjectivity
import «section 3».GammaGroundRVProductNormalForm
import «section 3».GammaGroundRVFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- Every actual RV[k] object is in the image of the concrete positive
tensor map. Geometry, finite labels, zero tags and original ground all remain. -/
theorem gammaGroundUnmeasuredTensor_object_preimage {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} (U : GammaGroundRVObject hc B k) :
    ∃ t : GammaGroundUnmeasuredPositiveTensor hc B,
      gammaGroundUnmeasuredTensorMap t = gammaGroundRVSemiringClass U := by
  obtain ⟨N,D,hdis,hcov⟩ := gammaGroundRV_product_normal_form hκ hs h00 hsmall hγsmall hΓ U.domain
  have hsub : ∀ i, (D i).source.carrier ⊆ U.domain.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  let W := fun i => U.restrict (D i).source (hsub i)
  have hparts : ∀ i, ∃ t : GammaGroundUnmeasuredPositiveTensor hc B,
      gammaGroundUnmeasuredTensorMap t = gammaGroundRVSemiringClass (W i) := by
    intro i
    by_cases hne : (W i).domain.carrier.Nonempty
    · exact gammaGroundUnmeasuredTensor_chart_preimage hκ hs h00 hsmall (W i) hne
        (D i).residue (D i).residue_finite (D i).gamma (D i).bijection
    · exact ⟨0,(map_zero _).trans (gammaGroundRVSemiringClass_of_empty (W i) (Set.not_nonempty_iff_eq_empty.mp hne)).symm⟩
  choose t ht using hparts
  refine ⟨∑ i, t i,?_⟩
  rw [map_sum]
  simp_rw [ht]
  exact (gammaGroundRVSemiringClass_finite_partition U (fun i => (D i).source) hdis hcov).symm

/-- Local proof of surjectivity of the concrete unmeasured positive
balanced tensor map. No HK theorem occurs in its hypotheses. -/
theorem gammaGroundUnmeasuredTensorMap_surjective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundUnmeasuredTensorMap (M := M) (hc := hc) (ground := B)) := by
  have hgen : ∀ o : GradedGammaGroundRVObject (M := M) hc B,
      ∃ t : GammaGroundUnmeasuredPositiveTensor hc B,
        gammaGroundUnmeasuredTensorMap t = PositiveGrothendieck.of (gammaGroundRVSemiringPresentation hc B) o := by
    rintro ⟨k,U⟩
    exact gammaGroundUnmeasuredTensor_object_preimage hκ hs h00 hsmall hγsmall hΓ U
  exact @positivePresentation_surjective_of_generators (GradedGammaGroundRVObject (M := M) hc B)
    (GammaGroundUnmeasuredPositiveTensor hc B) inferInstance (gammaGroundRVSemiringPresentation hc B)
    (gammaGroundUnmeasuredTensorMap (M := M) (hc := hc) (ground := B)) hgen

/-- Group completion preserves the locally proved tensor surjectivity. -/
theorem gammaGroundUnmeasuredGroupTensorMap_surjective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundUnmeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)) := by
  have hp := gammaGroundUnmeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ
  exact (ringCompletionMap_surjective _ hp).comp
    (ringCompletionTensorEquiv (R := GammaGroundFiniteGammaPositiveSemiring hc B)
      (A := GammaGroundRESDirectSum hc B) (B := GammaGroundGammaPositiveSemiring hc B)).symm.surjective
end DiamondIntegral.Section3
