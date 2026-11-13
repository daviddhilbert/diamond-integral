import «section 4».GammaAlternativeMaps
import «section 4».RVAlternativeTensorEvaluation
import «section 4».RESAlternativeForget
import «section 4».RVOrdinaryTensorEvaluation

/-! The alternative enlarged-target construction commutes with ordinary
geometric Euler evaluation after forgetting volume and imposing the
ordinary affine-line relation. This holds on the entire actual balanced
tensor; it does not presume global RV kernel descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RESAlternativeCompatibility
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem forget_weight (B : Base (M := M)) (a : GammaNamesSubgroup.additiveNames B) :
    RESAlternativeForget.forget B (RESAlternativeReduction.weightCharacter B (Multiplicative.ofAdd a)) = 1 :=
  RESAlternativeForget.measuredForget_weight B a

theorem forget_torus (B : Base (M := M)) :
    RESAlternativeForget.forget B (RESAlternativeReduction.torusClass B) =
      RESAlternativeForget.quotient B (RESOrdinaryReduction.torusClass B) :=
  RESAlternativeForget.measuredForget_torus B

theorem psi_forget (B : Base (M := M)) (p : GammaFunctionPolynomial.sourceRing B EulerKind.geometric) :
    RESAlternativeForget.forget B (RESAlternativePsi.psi B p) =
      GammaEulerEvaluation.polynomial B EulerKind.geometric
        (RESAlternativeForget.quotient B (RESOrdinaryReduction.torusClass B)) p := by
  have he := GammaAlternativeSpecialization.specialize_map_trivial B EulerKind.geometric
    (RESAlternativeReduction.weightCharacter B) (RESAlternativeReduction.torusClass B)
    (RESAlternativeReduction.weighted_torus B) (RESAlternativeForget.forget B) (forget_weight B) p
  rw [forget_torus] at he
  exact he

variable (h00 : M ⊨ Axioms.ACVF00)
  (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (hΓ : Section2.NontrivialDefinableGamma B)

theorem gamma_forget (x : GammaRVChartPresentation.ChartRing B) :
    RESAlternativeForget.forget B (GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ x) =
      RESAlternativeForget.quotient B (GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x) := by
  change RESAlternativeForget.forget B (RESAlternativePsi.psi B
    (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x)) =
      RESAlternativeForget.quotient B (GammaEulerEvaluation.polynomial B EulerKind.geometric
        (RESOrdinaryReduction.torusClass B)
        (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x))
  rw [psi_forget]
  exact (GammaEulerEvaluation.polynomial_map B EulerKind.geometric (RESAlternativeForget.quotient B)
    (RESOrdinaryReduction.torusClass B) _).symm

theorem tensor_forget (x : RVFiniteBalancedTensor.Source B) :
    RESAlternativeForget.forget B (RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ x) =
      RESAlternativeForget.quotient B (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [RVAlternativeTensorEvaluation.evaluation_tmul, RVOrdinaryTensorEvaluation.evaluation_tmul,
      map_mul, map_mul, RESAlternativeForget.forget_fromMeasured, gamma_forget]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end DiamondIntegral.Section4.RESAlternativeCompatibility
