import «section 3».MeasuredRVSemiring
import «section 3».RVGenerators

/-! The measured elementary relation is homogeneous of degree one.
Both objects carry the actual constant additive-zero Gamma volume form. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def measuredRVSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RingCon (MeasuredRVPositiveSemiring hc S) :=
  ringConGen (fun x y =>
    x = measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvOneObject S)) ∧
    y = measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvPositiveObject hc S)))

def measuredRVPrincipalElement (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    MeasuredRVGrothendieckRing hc S :=
  Algebra.GrothendieckAddGroup.of
      (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvOneObject S))) -
    Algebra.GrothendieckAddGroup.of
      (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvPositiveObject hc S)))

def measuredRVSpecialCompletionEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RingCompletion (measuredRVSpecialCongruence hc S).Quotient ≃+*
      MeasuredRVGrothendieckRing hc S ⧸ Ideal.span
        ({measuredRVPrincipalElement hc S} : Set (MeasuredRVGrothendieckRing hc S)) :=
  groupifiedMeasuredRelation
    (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvOneObject S)))
    (measuredRVSemiringClass hc (MeasuredRVObject.withZeroForm hc (rvPositiveObject hc S)))

end DiamondIntegral.Section3
