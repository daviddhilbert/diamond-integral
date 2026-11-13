import «section 4».RVBalancedSpecialClasses
import «section 4».GammaBoundedRVEmpty

/-! The actual balanced-tensor radius preimage is independent of its RV
lift choice. At radius zero it is already zero in the tensor source,
before comparison, evaluation or quotienting. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBalancedRadiusChoices
open GammaRVLifts RVRadiusGenerators RVPointChoices
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def withLift (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : RVBoundedBalancedTensor.Source B :=
  RVBoundedBalancedTensor.fromInteger B (RVRadiusTensor.radiusPreimage B γ hγ t)

theorem withLift_formula (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : withLift B γ hγ t =
    (1 ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVPresentation.objectClass (RVRadiusTensor.annulusChart B γ hγ)) +
      (RESChartRing.objectClass (pointRESChart B t.point t.definable) ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) -
      (RESChartRing.objectClass (pointRESChart B oneCode (oneCode_definable B)) ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) := by
  unfold withLift RVRadiusTensor.radiusPreimage
  rw [map_sub, map_add, RVBoundedBalancedTensor.fromInteger_tmul,
    RVBoundedBalancedTensor.fromInteger_tmul, RVBoundedBalancedTensor.fromInteger_tmul]

theorem withLift_independent (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t u : RadiusLift B γ) : withLift B γ hγ t = withLift B γ hγ u := by
  have hp : RESChartRing.objectClass (pointRESChart B t.point t.definable) =
      RESChartRing.objectClass (pointRESChart B u.point u.definable) :=
    RESChartRing.objectClass_iso (same_value_iso B t.point u.point t.definable u.definable (t.value_eq.trans u.value_eq.symm))
  rw [withLift_formula, withLift_formula, hp]

theorem canonical_eq_withLift (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : RVBalancedSpecialClasses.radiusPreimage B γ hγ = withLift B γ hγ t :=
  withLift_independent B γ hγ _ t

theorem annulus_zero_class (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    GammaBoundedRVPresentation.objectClass (RVRadiusTensor.annulusChart B 1 hγ) = 0 :=
  GammaBoundedRVEmpty.class_empty_support B (RVRadiusTensor.annulusChart B 1 hγ) GammaRadiusAnnulus.annulus_one

theorem withLift_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B)
    (t : RadiusLift B 1) : withLift B 1 hγ t = 0 := by
  rw [withLift_independent B 1 hγ t (unitLift B), withLift_formula, annulus_zero_class]
  simp only [TensorProduct.tmul_zero, zero_add]
  exact sub_self _

theorem canonical_zero (B : Base (M := M)) (hγ : (1 : Values.Gamma (M := M)) ∈ admissibleRadii B) :
    RVBalancedSpecialClasses.radiusPreimage B 1 hγ = 0 :=
  (canonical_eq_withLift B 1 hγ (unitLift B)).trans (withLift_zero B hγ (unitLift B))

end DiamondIntegral.Section4.RVBalancedRadiusChoices
