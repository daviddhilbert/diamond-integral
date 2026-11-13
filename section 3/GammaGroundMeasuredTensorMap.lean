import «section 3».GammaGroundMeasuredFiniteGammaSemiringSquare
import «section 3».CompletionTensor
/-! The canonical measured balanced tensor map of Proposition 3.18.
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

instance gammaGroundMeasuredFiniteGammaRESAlgebra : Algebra (GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground) (GammaGroundMeasuredRESDirectSum (M := M) hc ground) :=
  (gammaGroundMeasuredFiniteGammaToRESSemiring (hc := hc) (ground := ground)).toAlgebra

instance gammaGroundMeasuredFiniteGammaGammaAlgebra : Algebra (GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground) (GammaGroundMeasuredGammaPositiveSemiring hc ground) :=
  (gammaGroundMeasuredFiniteGammaToGammaSemiring (hc := hc) (ground := ground)).toAlgebra

abbrev GammaGroundMeasuredPositiveTensor (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  GammaGroundMeasuredRESDirectSum (M := M) hc ground ⊗[GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground] GammaGroundMeasuredGammaPositiveSemiring hc ground

def gammaGroundMeasuredTensorMap : GammaGroundMeasuredPositiveTensor hc ground →+* GammaGroundMeasuredRVPositiveSemiring (M := M) hc ground :=
  balancedSquareMap gammaGroundMeasuredRESToRVSemiring gammaGroundMeasuredGammaToRVSemiring gammaGroundMeasuredFiniteGamma_semiring_square

@[simp] theorem gammaGroundMeasuredTensorMap_tmul (a : GammaGroundMeasuredRESDirectSum (M := M) hc ground) (b : GammaGroundMeasuredGammaPositiveSemiring hc ground) :
    gammaGroundMeasuredTensorMap (a ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground] b) =
      gammaGroundMeasuredRESToRVSemiring a * gammaGroundMeasuredGammaToRVSemiring b := rfl

theorem gammaGroundMeasuredTensorMap_objects {k l : ℕ} (A : GammaGroundMeasuredRESObject (M := M) hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    gammaGroundMeasuredTensorMap (gammaGroundMeasuredRESDirectSumClass A ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground] gammaGroundMeasuredGammaSemiringClass B) =
      gammaGroundMeasuredRVSemiringClass (A.obj.product B.rvLift) := by
  rw [gammaGroundMeasuredTensorMap_tmul, gammaGroundMeasuredRESToRVSemiring_class, gammaGroundMeasuredGammaToRVSemiring_class, gammaGroundMeasuredRVSemiringClass_product]

def gammaGroundMeasuredGroupTensorMap :
    RingCompletion (GammaGroundMeasuredRESDirectSum (M := M) hc ground) ⊗[GammaGroundMeasuredFiniteGammaGrothendieckRing hc ground]
      GammaGroundMeasuredGammaGrothendieckRing hc ground →+* GammaGroundMeasuredRVGrothendieckRing (M := M) hc ground :=
  (ringCompletionMap (gammaGroundMeasuredTensorMap (hc := hc) (ground := ground))).comp
    (ringCompletionTensorEquiv (R := GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground)
      (A := GammaGroundMeasuredRESDirectSum hc ground) (B := GammaGroundMeasuredGammaPositiveSemiring hc ground)).symm.toRingHom

end DiamondIntegral.Section3
