import «section 3».GammaGroundFiniteGammaSemiringSquare
import «section 3».CompletionTensor
/-! The canonical unmeasured balanced tensor map of Proposition 3.18.
Its bijectivity is a separate geometric decomposition obligation. -/
set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
namespace DiamondIntegral.Section3
open scoped TensorProduct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

instance gammaGroundFiniteGammaRESAlgebra : Algebra (GammaGroundFiniteGammaPositiveSemiring hc ground) (GammaGroundRESDirectSum (M := M) hc ground) :=
  (gammaGroundFiniteGammaToRESSemiring (hc := hc) (ground := ground)).toAlgebra

instance gammaGroundFiniteGammaGammaAlgebra : Algebra (GammaGroundFiniteGammaPositiveSemiring hc ground) (GammaGroundGammaPositiveSemiring hc ground) :=
  (gammaGroundFiniteGammaToGammaSemiring (hc := hc) (ground := ground)).toAlgebra

abbrev GammaGroundUnmeasuredPositiveTensor (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  GammaGroundRESDirectSum (M := M) hc ground ⊗[GammaGroundFiniteGammaPositiveSemiring hc ground] GammaGroundGammaPositiveSemiring hc ground

def gammaGroundUnmeasuredTensorMap : GammaGroundUnmeasuredPositiveTensor hc ground →+* GammaGroundRVPositiveSemiring (M := M) hc ground :=
  balancedSquareMap gammaGroundRESToRVSemiring gammaGroundGammaToRVSemiring gammaGroundFiniteGamma_semiring_square

@[simp] theorem gammaGroundUnmeasuredTensorMap_tmul (a : GammaGroundRESDirectSum (M := M) hc ground) (b : GammaGroundGammaPositiveSemiring hc ground) :
    gammaGroundUnmeasuredTensorMap (a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc ground] b) =
      gammaGroundRESToRVSemiring a * gammaGroundGammaToRVSemiring b := rfl

theorem gammaGroundUnmeasuredTensorMap_objects {k l : ℕ} (A : GammaGroundRESObject (M := M) hc ground k) (B : GammaGroundGammaObject hc ground l) :
    gammaGroundUnmeasuredTensorMap (gammaGroundRESDirectSumClass A ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc ground] gammaGroundGammaSemiringClass B) =
      gammaGroundRVSemiringClass (A.obj.product B.rvLift) := by
  rw [gammaGroundUnmeasuredTensorMap_tmul, gammaGroundRESToRVSemiring_class, gammaGroundGammaToRVSemiring_class, gammaGroundRVSemiringClass_product]

def gammaGroundUnmeasuredGroupTensorMap :
    RingCompletion (GammaGroundRESDirectSum (M := M) hc ground) ⊗[GammaGroundFiniteGammaGrothendieckRing hc ground]
      GammaGroundGammaGrothendieckRing hc ground →+* GammaGroundRVGrothendieckRing (M := M) hc ground :=
  (ringCompletionMap (gammaGroundUnmeasuredTensorMap (hc := hc) (ground := ground))).comp
    (ringCompletionTensorEquiv (R := GammaGroundFiniteGammaPositiveSemiring hc ground)
      (A := GammaGroundRESDirectSum hc ground) (B := GammaGroundGammaPositiveSemiring hc ground)).symm.toRingHom

end DiamondIntegral.Section3
