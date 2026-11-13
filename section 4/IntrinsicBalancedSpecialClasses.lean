import «section 4».IntrinsicBalancedEvaluations
import «section 4».RVBalancedSpecialGradings
import «section 4».RVBalancedRadiusChoices
import «section 4».RVBoundedOrdinaryRadius

/-! The actual P, h and accepted-radius preimages in the intrinsic
balanced tensors, with degree, comparison and evaluation calculations.
No assertion of global RV descent or point nonvanishing is made. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedSpecialClasses
open IntrinsicBalancedTensors IntrinsicFiniteGammaAlgebras GammaRVLifts RVRadiusGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pPreimage (B : Base (M := M)) : Source B := (equivalence B).symm (RVBalancedSpecialClasses.pPreimage B)
def hPreimage (B : Base (M := M)) : Source B := (equivalence B).symm (RVBalancedSpecialClasses.hPreimage B)
def radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) : BoundedSource B :=
  (boundedEquivalence B).symm (RVBalancedSpecialClasses.radiusPreimage B γ hγ)
def radiusWithLift (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : BoundedSource B :=
  (boundedEquivalence B).symm (RVBalancedRadiusChoices.withLift B γ hγ t)

theorem radiusWithLift_independent (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) (t u : RadiusLift B γ) :
    radiusWithLift B γ hγ t = radiusWithLift B γ hγ u :=
  congrArg (boundedEquivalence B).symm (RVBalancedRadiusChoices.withLift_independent B γ hγ t u)

theorem radius_eq_withLift (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    radiusPreimage B γ hγ = radiusWithLift B γ hγ t :=
  congrArg (boundedEquivalence B).symm (RVBalancedRadiusChoices.canonical_eq_withLift B γ hγ t)

theorem radius_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) : radiusPreimage B 1 hγ = 0 := by
  unfold radiusPreimage
  rw [RVBalancedRadiusChoices.canonical_zero, map_zero]

theorem pPreimage_mem (B : Base (M := M)) : pPreimage B ∈ IntrinsicBalancedGradings.measuredPiece B 1 :=
  IntrinsicBalancedGradings.inverse_mem B (RVBalancedSpecialGradings.pPreimage_mem B)
theorem hPreimage_mem (B : Base (M := M)) : hPreimage B ∈ IntrinsicBalancedGradings.measuredPiece B 1 :=
  IntrinsicBalancedGradings.inverse_mem B (RVBalancedSpecialGradings.hPreimage_mem B)
theorem radiusPreimage_mem (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    radiusPreimage B γ hγ ∈ IntrinsicBalancedGradings.boundedPiece B 1 :=
  IntrinsicBalancedGradings.boundedInverse_mem B (RVBalancedSpecialGradings.radiusPreimage_mem B γ hγ)

theorem comparison_pPreimage (B : Base (M := M)) : comparison B (pPreimage B) = RVDisjointPQuotients.Measured.pClass B := by
  change (RVDisjointPresentation.equivalence B).symm (RVFiniteBalancedTensor.comparison B
    (equivalence B ((equivalence B).symm (RVBalancedSpecialClasses.pPreimage B)))) = _
  rw [AlgEquiv.apply_symm_apply, RVBalancedSpecialClasses.comparison_pPreimage]
  apply (RVDisjointPresentation.equivalence B).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RVDisjointPQuotients.Measured.toChart_pClass B).symm

theorem comparison_radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    boundedComparison B (radiusPreimage B γ hγ) = RVDisjointRadiusQuotient.pGamma B γ hγ := by
  change (RVBoundedDisjointPresentation.equivalence B).symm (RVBoundedBalancedTensor.comparison B
    (boundedEquivalence B ((boundedEquivalence B).symm (RVBalancedSpecialClasses.radiusPreimage B γ hγ)))) = _
  rw [AlgEquiv.apply_symm_apply, RVBalancedSpecialClasses.comparison_radiusPreimage]
  apply (RVBoundedDisjointPresentation.equivalence B).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RVDisjointRadiusQuotient.toChart_pGamma B γ hγ).symm

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_pPreimage (k : EulerKind) :
    IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ k (pPreimage B) = 0 := by
  change (RESDisjointReduction.Measured.equivalence B).symm
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k
      (equivalence B ((equivalence B).symm (RVBalancedSpecialClasses.pPreimage B)))) = 0
  rw [AlgEquiv.apply_symm_apply, RVBalancedSpecialClasses.evaluation_pPreimage, map_zero]

theorem evaluation_h_geometric :
    IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (hPreimage B) =
      RESDisjointReduction.Measured.quotient B (RESDisjointPresentation.objectClass (RESFibreObjects.point B)) := by
  change (RESDisjointReduction.Measured.equivalence B).symm
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (equivalence B ((equivalence B).symm (RVBalancedSpecialClasses.hPreimage B)))) = _
  rw [AlgEquiv.apply_symm_apply, RVBalancedSpecialClasses.evaluation_hPreimage_geometric]
  apply (RESDisjointReduction.Measured.equivalence B).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RESDisjointReduction.Measured.equivalence_class B (RESFibreObjects.point B)).symm

theorem evaluation_h_bounded :
    IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (hPreimage B) = 0 := by
  change (RESDisjointReduction.Measured.equivalence B).symm
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded
      (equivalence B ((equivalence B).symm (RVBalancedSpecialClasses.hPreimage B)))) = 0
  rw [AlgEquiv.apply_symm_apply, RVBalancedSpecialClasses.evaluation_hPreimage_bounded, map_zero]

theorem evaluation_radiusPreimage (k : EulerKind) (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) :
    IntrinsicBalancedEvaluations.bounded h00 linear hκ hs B hr hγ hΓ k (radiusPreimage B γ hγ') = 0 := by
  change (RESDisjointReduction.Ordinary.equivalence B).symm
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (boundedEquivalence B ((boundedEquivalence B).symm (RVBalancedSpecialClasses.radiusPreimage B γ hγ')))) = 0
  rw [AlgEquiv.apply_symm_apply, RVBoundedOrdinaryRadius.radius_evaluation, map_zero]

end DiamondIntegral.Section4.IntrinsicBalancedSpecialClasses
