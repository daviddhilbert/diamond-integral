import «section 3».GammaGroundUnmeasuredTensorMap
import «section 3».GammaGroundMeasuredTensorMap
import «section 3».GammaFixedPrefixProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3

/-- Multiplication by a shared scalar balances across a positive tensor. -/
theorem tensor_algebraMap_factor_balance {R A D : Type}
    [CommSemiring R] [CommSemiring A] [CommSemiring D] [Algebra R A] [Algebra R D]
    (a : A) (t : R) (b : D) :
    a ⊗ₜ[R] (algebraMap R D t * b) = (a * algebraMap R A t) ⊗ₜ[R] b := by
  rw [mul_comm a]
  simpa only [Algebra.smul_def] using (TensorProduct.smul_tmul t a b).symm

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r k l : ℕ}

/-- Move any actual finite Gamma factor to RES by the positive tensor
balancing relation, preserving its full grading. -/
theorem gammaGroundUnmeasuredTensor_finite_factor_absorption
    (X : GammaGroundRESObject hc B r) (F : GammaGroundFiniteGammaObject hc B k)
    (W : GammaGroundGammaObject hc B l) :
    gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        (gammaGroundGammaSemiringClass F.obj * gammaGroundGammaSemiringClass W) =
      gammaGroundRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass W := by
  rw [gammaGroundRESDirectSumClass_product,
    ← gammaGroundFiniteGammaToGammaSemiring_class F,← gammaGroundFiniteGammaToRESSemiring_class F]
  let a := gammaGroundRESDirectSumClass X
  let b := gammaGroundGammaSemiringClass W
  let t := gammaGroundFiniteGammaSemiringClass F
  change a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    (algebraMap (GammaGroundFiniteGammaPositiveSemiring hc B) (GammaGroundGammaPositiveSemiring hc B) t * b) =
      (a * algebraMap (GammaGroundFiniteGammaPositiveSemiring hc B) (GammaGroundRESDirectSum hc B) t) ⊗ₜ[_] b
  exact tensor_algebraMap_factor_balance a t b

/-- The same positive balancing identity retains all measured finite
Gamma forms, including degree-zero coefficients. -/
theorem gammaGroundMeasuredTensor_finite_factor_absorption
    (X : GammaGroundMeasuredRESObject hc B r) (F : GammaGroundMeasuredFiniteGammaObject hc B k)
    (W : GammaGroundMeasuredGammaObject hc B l) :
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        (gammaGroundMeasuredGammaSemiringClass F.obj * gammaGroundMeasuredGammaSemiringClass W) =
      gammaGroundMeasuredRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass W := by
  rw [gammaGroundMeasuredRESDirectSumClass_product,
    ← gammaGroundMeasuredFiniteGammaToGammaSemiring_class F,← gammaGroundMeasuredFiniteGammaToRESSemiring_class F]
  let a := gammaGroundMeasuredRESDirectSumClass X
  let b := gammaGroundMeasuredGammaSemiringClass W
  let t := gammaGroundMeasuredFiniteGammaSemiringClass F
  change a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    (algebraMap (GammaGroundMeasuredFiniteGammaPositiveSemiring hc B) (GammaGroundMeasuredGammaPositiveSemiring hc B) t * b) =
      (a * algebraMap (GammaGroundMeasuredFiniteGammaPositiveSemiring hc B) (GammaGroundMeasuredRESDirectSum hc B) t) ⊗ₜ[_] b
  exact tensor_algebraMap_factor_balance a t b

/-- A fixed Gamma prefix is absorbed into RES without subtracting tensor
classes or discarding the prefix degree. -/
theorem gammaGroundUnmeasuredTensor_fixed_prefix_absorption
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaPiece hc B (k+l))
    (δ : Fin k → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hfixed : ∀ γ : Fin (k+l) → Values.Gamma (M := M),
      γ ∈ G.carrier → ∀ i, γ (Fin.castAdd l i) = δ i) :
    ∃ F : GammaGroundFiniteGammaObject hc B k, ∃ W : GammaGroundGammaPiece hc B l,
      gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        gammaGroundRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single W) := by
  obtain ⟨F,W,hG⟩ := gammaGroundGammaSemiringClass_fixed_prefix G δ hδ hfixed
  refine ⟨F,W,?_⟩
  rw [hG]
  exact gammaGroundUnmeasuredTensor_finite_factor_absorption X F (GammaGroundGammaObject.single W)
end DiamondIntegral.Section3
