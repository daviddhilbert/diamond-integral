import «section 3».FiniteGammaSemiringSquare
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

instance finiteGammaRESAlgebra : Algebra (FiniteGammaPositiveSemiring hc S) (RESDirectSum (M := M) S) :=
  (finiteGammaToRESSemiring (hc := hc) (S := S)).toAlgebra

instance finiteGammaGammaAlgebra : Algebra (FiniteGammaPositiveSemiring hc S) (GammaPositiveSemiring hc S) :=
  (finiteGammaToGammaSemiring (hc := hc) (S := S)).toAlgebra

abbrev UnmeasuredPositiveTensor (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  RESDirectSum (M := M) S ⊗[FiniteGammaPositiveSemiring hc S] GammaPositiveSemiring hc S

def unmeasuredTensorMap : UnmeasuredPositiveTensor hc S →+* RVPositiveSemiring (M := M) S :=
  balancedSquareMap resToRVSemiring gammaToRVSemiring finiteGamma_semiring_square

@[simp] theorem unmeasuredTensorMap_tmul (a : RESDirectSum (M := M) S) (b : GammaPositiveSemiring hc S) :
    unmeasuredTensorMap (a ⊗ₜ[FiniteGammaPositiveSemiring hc S] b) =
      resToRVSemiring a * gammaToRVSemiring b := rfl

theorem unmeasuredTensorMap_objects {k l : ℕ} (A : RESObject (M := M) S k) (B : GammaObject hc S l) :
    unmeasuredTensorMap (resDirectSumClass A ⊗ₜ[FiniteGammaPositiveSemiring hc S] gammaSemiringClass B) =
      rvSemiringClass (A.obj.product B.rvLift) := by
  rw [unmeasuredTensorMap_tmul, resToRVSemiring_class, gammaToRVSemiring_class, rvSemiringClass_product]

def unmeasuredGroupTensorMap :
    RingCompletion (RESDirectSum (M := M) S) ⊗[FiniteGammaGrothendieckRing hc S]
      GammaGrothendieckRing hc S →+* RVGrothendieckRing (M := M) S :=
  (ringCompletionMap (unmeasuredTensorMap (hc := hc) (S := S))).comp
    (ringCompletionTensorEquiv (R := FiniteGammaPositiveSemiring hc S)
      (A := RESDirectSum S) (B := GammaPositiveSemiring hc S)).symm.toRingHom

end DiamondIntegral.Section3
