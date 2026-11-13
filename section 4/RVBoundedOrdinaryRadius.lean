import «section 4».RVBoundedOrdinaryEvaluation
import «section 4».RVBalancedRadiusChoices
import «section 4».RVBalancedRadiusQuotient

/-! Direct bounded ordinary evaluation kills all accepted radius
relations and descends as a graded map on the tensor radius quotient,
without a canonical-structure premise. The exact original-base
RV-liftable radius set and its zero-radius case are retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBoundedOrdinaryRadius
open GammaRVLifts RVRadiusGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem annulus_evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) :
    GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaBoundedRVMaps.forget B (GammaBoundedRVPresentation.objectClass (RVRadiusTensor.annulusChart B γ hγ'))) = 0 := by
  rw [GammaBoundedRVMaps.forget_class, GammaOrdinaryEvaluation.evaluation_class]
  change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
    (GammaRadiusAnnulus.annulusFamily B γ hγ') : RESOrdinaryReduction.ReducedRing B) *
      RESOrdinaryReduction.torusClass B ^ 1 = 0
  rw [GammaRadiusAnnulus.integral_annulus h00 hκ hs B hr hγ k γ hγ', Int.cast_zero, zero_mul]

theorem radius_evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) :
    RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (RVBalancedSpecialClasses.radiusPreimage B γ hγ') = 0 := by
  let t := Classical.choice (radiusLift_exists B γ hγ')
  rw [RVBalancedRadiusChoices.canonical_eq_withLift B γ hγ' t, RVBalancedRadiusChoices.withLift_formula]
  simp only [map_sub, map_add, RVBoundedOrdinaryEvaluation.evaluation_tmul, map_one, one_mul, mul_one]
  rw [annulus_evaluation, RESOrdinaryPoints.forget_point_classes B t.point oneCode t.definable (oneCode_definable B),
    zero_add, sub_self]

theorem ideal_le_ker (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    RVBalancedRadiusIdeal.radiusIdeal B ≤ RingHom.ker
      (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ', rfl⟩
  exact radius_evaluation h00 linear hκ hs B hr hγ hΓ k γ hγ'

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (RVBalancedRadiusQuotient.piece B) (RESReductionGradings.ordinaryPiece B) :=
  (RVBalancedGradings.boundedCoaction B).gradedQuotientLift (RESReductionGradings.ordinaryCoaction B)
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom
    (RVBalancedRadiusIdeal.radiusIdeal B) (RVBalancedRadiusQuotient.ideal_coefficients B)
    (fun _ hx => ideal_le_ker h00 linear hκ hs B hr hγ hΓ k hx)
    (fun _ _ hx => (RVBoundedOrdinaryEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).map_mem hx)

theorem evaluation_mk (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RVBoundedBalancedTensor.Source B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (RVBalancedRadiusQuotient.quotient B x) =
      RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k x := rfl

theorem evaluation_res (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (RVBalancedRadiusQuotient.ofRES B x) = RESOrdinaryReduction.forget B x :=
  RVBoundedOrdinaryEvaluation.evaluation_res h00 linear hκ hs B hr hγ hΓ k x

theorem evaluation_independent_kind (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom = (evaluation h00 linear hκ hs B hr hγ hΓ l).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (RVBoundedOrdinaryEvaluation.evaluation_independent_kind h00 linear hκ hs B hr hγ hΓ k l) x

theorem evaluation_eq_previous (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom =
      (RVBalancedRadiusQuotient.evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (RVBoundedOrdinaryEvaluation.evaluation_eq_previous hc h00 linear hκ hs B hr hγ hΓ k) x

end DiamondIntegral.Section4.RVBoundedOrdinaryRadius
