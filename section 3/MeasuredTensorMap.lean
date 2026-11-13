import «section 3».MeasuredFiniteGammaSemiringSquare
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

instance measuredFiniteGammaRESAlgebra : Algebra (MeasuredFiniteGammaPositiveSemiring hc S) (MeasuredRESDirectSum (M := M) hc S) :=
  (measuredFiniteGammaToRESSemiring (hc := hc) (S := S)).toAlgebra

instance measuredFiniteGammaGammaAlgebra : Algebra (MeasuredFiniteGammaPositiveSemiring hc S) (MeasuredGammaPositiveSemiring hc S) :=
  (measuredFiniteGammaToGammaSemiring (hc := hc) (S := S)).toAlgebra

abbrev MeasuredPositiveTensor (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  MeasuredRESDirectSum (M := M) hc S ⊗[MeasuredFiniteGammaPositiveSemiring hc S] MeasuredGammaPositiveSemiring hc S

def measuredTensorMap : MeasuredPositiveTensor hc S →+* MeasuredRVPositiveSemiring (M := M) hc S :=
  balancedSquareMap measuredResToRVSemiring measuredGammaToRVSemiring measuredFiniteGamma_semiring_square

@[simp] theorem measuredTensorMap_tmul (a : MeasuredRESDirectSum (M := M) hc S) (b : MeasuredGammaPositiveSemiring hc S) :
    measuredTensorMap (a ⊗ₜ[MeasuredFiniteGammaPositiveSemiring hc S] b) =
      measuredResToRVSemiring a * measuredGammaToRVSemiring b := rfl

theorem measuredTensorMap_objects {k l : ℕ} (A : MeasuredRESObject (M := M) S k) (B : MeasuredGammaObject hc S l) :
    measuredTensorMap (measuredResDirectSumClass hc A ⊗ₜ[MeasuredFiniteGammaPositiveSemiring hc S] measuredGammaSemiringClass B) =
      measuredRVSemiringClass hc (A.obj.product hc B.rvLift) := by
  rw [measuredTensorMap_tmul, measuredResToRVSemiring_class, measuredGammaToRVSemiring_class, measuredRVSemiringClass_product hc]

def measuredGroupTensorMap :
    RingCompletion (MeasuredRESDirectSum (M := M) hc S) ⊗[MeasuredFiniteGammaGrothendieckRing hc S]
      MeasuredGammaGrothendieckRing hc S →+* MeasuredRVGrothendieckRing (M := M) hc S :=
  (ringCompletionMap (measuredTensorMap (hc := hc) (S := S))).comp
    (ringCompletionTensorEquiv (R := MeasuredFiniteGammaPositiveSemiring hc S)
      (A := MeasuredRESDirectSum hc S) (B := MeasuredGammaPositiveSemiring hc S)).symm.toRingHom

end DiamondIntegral.Section3
