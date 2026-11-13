import «section 3».GammaGroundMeasuredRVSemiring
import «section 3».GammaGroundRVGenerators

/-! The actual homogeneous measured principal relation over the Gamma
ground: both degree-one objects have constant additive-zero volume. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaGroundMeasuredRVOne (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredRVObject hc ground 1 :=
  .withZeroForm (.ofReal (rvOneObject ground.real))

def gammaGroundMeasuredRVPositive (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredRVObject hc ground 1 :=
  .withZeroForm (.ofReal (rvPositiveObject hc ground.real))

def gammaGroundMeasuredRVSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : RingCon (GammaGroundMeasuredRVPositiveSemiring hc ground) :=
  ringConGen (fun x y => x = gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc ground) ∧
    y = gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc ground))

def gammaGroundMeasuredRVPrincipalElement (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredRVGrothendieckRing hc ground :=
  Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc ground)) -
    Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc ground))

def gammaGroundMeasuredRVSpecialCompletionEquiv (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) :
    RingCompletion (gammaGroundMeasuredRVSpecialCongruence hc ground).Quotient ≃+*
      GammaGroundMeasuredRVGrothendieckRing hc ground ⧸ Ideal.span
        ({gammaGroundMeasuredRVPrincipalElement hc ground} : Set (GammaGroundMeasuredRVGrothendieckRing hc ground)) :=
  groupifiedMeasuredRelation (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVOne hc ground))
    (gammaGroundMeasuredRVSemiringClass (gammaGroundMeasuredRVPositive hc ground))

end DiamondIntegral.Section3
