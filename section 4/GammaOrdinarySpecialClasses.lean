import «section 4».GammaOrdinaryEvaluation
import «section 4».RVMeasuredSpecialClasses

/-! The ordinary evaluation of the actual positive ray, with either
constant or compensating volume, is chi(ray) times the torus. This
retains the distinct ordinary and measured target conventions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinarySpecialClasses
open GammaCounterweightedRay GammaDefinableMaps GammaWeightProfiles
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem positiveRay_integral (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
      (GammaIndicators.indicatorFamily B positiveRay (positiveRay_definable B)) = k.rayValue := by
  have he := profile_integral h00 linear hκ hs B hr hγ hΓ k positiveRay (positiveRay_definable B)
    (fun _ => 1) (constant_definable B 1 (GammaGroupNames.one_definable_base B))
  rw [GammaUnaryIdentityProfile.profile_positiveRay, EulerFunction.totalEuler_ray] at he
  exact he.symm

theorem evaluation_ray (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.rayChart B)) =
      (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  rw [GammaOrdinaryEvaluation.evaluation_class]
  change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
    (GammaIndicators.indicatorFamily B positiveRay (positiveRay_definable B)) : RESOrdinaryReduction.ReducedRing B) *
      RESOrdinaryReduction.torusClass B ^ 1 = _
  rw [positiveRay_integral h00 linear hκ hs B hr hγ hΓ k, pow_one]

theorem evaluation_counterweighted (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.counterweightedChart B)) =
      (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  have he : GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
      (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.counterweightedChart B)) =
      GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
        (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.rayChart B)) := by
    rw [GammaOrdinaryEvaluation.evaluation_class, GammaOrdinaryEvaluation.evaluation_class]
    rfl
  exact he.trans (evaluation_ray h00 linear hκ hs B hr hγ hΓ k)

end DiamondIntegral.Section4.GammaOrdinarySpecialClasses
