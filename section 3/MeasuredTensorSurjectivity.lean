import «section 3».MeasuredTensorChart
import «section 3».CompletionSurjectivity
import «section 3».PositivePresentationSurjectivity
import «section 3».GammaGroundRVFormNormalForm
import «section 3».GammaGroundMeasuredRVFinitePartitions
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
theorem gammaGroundMeasuredTensor_object_preimage {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) :
    ∃ t : GammaGroundMeasuredPositiveTensor hc B,
      gammaGroundMeasuredTensorMap t = gammaGroundMeasuredRVSemiringClass U := by
  let w := fun x => if hx : x ∈ U.underlying.domain.carrier then U.combinedWeight ⟨x,hx⟩ else 1
  have hw : ∀ a : U.underlying.domain, w a.val = (U.combinedWeightForm a).val := by
    intro a
    rw [show w a.val = U.combinedWeight a from dif_pos a.property]
    exact (U.combinedWeightForm_value a).symm
  obtain ⟨N,D,hdis,hcov⟩ := gammaGroundRV_form_normal_form hκ hs h00 hsmall hγsmall hΓ
    U.underlying.domain U.combinedWeightForm w hw
  have hsub : ∀ i, (D i).source.carrier ⊆ U.underlying.domain.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  let W := fun i => U.restrict (D i).source (hsub i)
  have hparts : ∀ i, ∃ t : GammaGroundMeasuredPositiveTensor hc B,
      gammaGroundMeasuredTensorMap t = gammaGroundMeasuredRVSemiringClass (W i) := by
    intro i
    by_cases hne : (W i).underlying.domain.carrier.Nonempty
    · exact gammaGroundMeasuredTensor_chart_preimage hκ hs h00 hsmall (W i) hne
        (D i).residue (D i).residue_finite (D i).gamma (D i).weight (D i).weight_definable
        (D i).bijection (fun a => by
          have he := (D i).preserves a
          change w a.val = _ at he
          rw [show w a.val = (W i).combinedWeight a from dif_pos (hsub i a.property)] at he
          exact he)
    · exact ⟨0,(map_zero _).trans (gammaGroundMeasuredRVSemiringClass_of_empty (W i) (Set.not_nonempty_iff_eq_empty.mp hne)).symm⟩
  choose t ht using hparts
  refine ⟨∑ i, t i,?_⟩
  rw [map_sum]
  simp_rw [ht]
  exact (gammaGroundMeasuredRVSemiringClass_finite_partition U (fun i => (D i).source) hdis hcov).symm

/-- Local proof of surjectivity of the concrete measured positive
balanced tensor map. No HK theorem occurs in its hypotheses. -/
theorem gammaGroundMeasuredTensorMap_surjective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundMeasuredTensorMap (M := M) (hc := hc) (ground := B)) := by
  have hgen : ∀ o : GradedGammaGroundMeasuredRVObject (M := M) hc B,
      ∃ t : GammaGroundMeasuredPositiveTensor hc B,
        gammaGroundMeasuredTensorMap t = PositiveGrothendieck.of (gammaGroundMeasuredRVSemiringPresentation hc B) o := by
    rintro ⟨k,U⟩
    exact gammaGroundMeasuredTensor_object_preimage hκ hs h00 hsmall hγsmall hΓ U
  exact @positivePresentation_surjective_of_generators (GradedGammaGroundMeasuredRVObject (M := M) hc B)
    (GammaGroundMeasuredPositiveTensor hc B) inferInstance (gammaGroundMeasuredRVSemiringPresentation hc B)
    (gammaGroundMeasuredTensorMap (M := M) (hc := hc) (ground := B)) hgen

/-- Group completion preserves the locally proved tensor surjectivity. -/
theorem gammaGroundMeasuredGroupTensorMap_surjective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (gammaGroundMeasuredGroupTensorMap (M := M) (hc := hc) (ground := B)) := by
  have hp := gammaGroundMeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ
  exact (ringCompletionMap_surjective _ hp).comp
    (ringCompletionTensorEquiv (R := GammaGroundMeasuredFiniteGammaPositiveSemiring hc B)
      (A := GammaGroundMeasuredRESDirectSum hc B) (B := GammaGroundMeasuredGammaPositiveSemiring hc B)).symm.surjective
end DiamondIntegral.Section3
