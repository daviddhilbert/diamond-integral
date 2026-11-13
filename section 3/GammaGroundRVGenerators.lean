import «section 3».GammaGroundRVSemiring
import «section 3».RVGenerators
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaGroundRVSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    RingCon (GammaGroundRVPositiveSemiring (M := M) hc ground) :=
  ringConGen (fun x y => x = gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real)) ∧
    y = gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)) + 1)

def gammaGroundRVPrincipalElement (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundRVGrothendieckRing (M := M) hc ground :=
  Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real))) -
    Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)))

def gammaGroundRVSpecialCompletionEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    RingCompletion (gammaGroundRVSpecialCongruence hc ground).Quotient ≃+*
      GammaGroundRVGrothendieckRing hc ground ⧸ Ideal.span ({gammaGroundRVPrincipalElement hc ground - 1} : Set (GammaGroundRVGrothendieckRing hc ground)) :=
  groupifiedUnmeasuredRelation (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvOneObject ground.real))) (gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (ground := ground) (rvPositiveObject hc ground.real)))


end DiamondIntegral.Section3
