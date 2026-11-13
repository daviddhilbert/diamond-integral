import «section 3».GammaGroundAnnulusRingVanishing
import «section 3».GammaGroundMeasuredRVForgetting
import «section 3».GammaGroundDefinablePoints
import «section 3».IdealPullbackKernel
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open Algebra.GrothendieckAddGroup
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- Exactly the radius data used in the annular relation: a nonnegative
original-ground Gamma value and its stipulated definable RV multiplier. -/
structure GammaGroundAnnularRadius (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) where
  value : Values.Gamma (M := M)
  definable : GammaDefinableClosureAtBase B value
  nonnegative : 1 ≤ value
  multiplier : Fin 1 → (CanonicalRV.RVSort M)ˣ
  multiplier_definable : GammaGroundDefinable hc B (rawRVUnitSpace 1) {multiplier}
  multiplier_value : rvUnitValueHom (multiplier 0) = value

/-- The annular expression with arbitrary forms on its two actual
singleton RV objects. Forgetting forms retains the underlying domains. -/
def gammaGroundMeasuredAnnularElement (d : GammaGroundAnnularRadius hc B)
    (P Q : GammaGroundMeasuredRVObject hc B 1) : GammaGroundMeasuredRVGrothendieckRing hc B :=
  of (gammaGroundMeasuredRVSemiringClass (.withZeroForm
    (gammaGroundGammaRVCodeLift (gammaGroundGammaAnnulus d.value d.definable)))) +
      of (gammaGroundMeasuredRVSemiringClass P) - of (gammaGroundMeasuredRVSemiringClass Q)

/-- Every stipulated annular generator vanishes in the full unmeasured
ring. This includes radius zero and uses unbounded tails only there. -/
theorem gammaGroundMeasuredAnnularElement_forget_zero
    (d : GammaGroundAnnularRadius hc B) (P Q : GammaGroundMeasuredRVObject hc B 1)
    (p : P.underlying.domain) (q : Q.underlying.domain)
    (hP : ∀ a : P.underlying.domain, a = p) (hQ : ∀ a : Q.underlying.domain, a = q) :
    gammaGroundMeasuredRVForgetRing (gammaGroundMeasuredAnnularElement d P Q) = 0 := by
  have hA := gammaGroundRVAnnulus_ring_zero d.value d.definable d.nonnegative
    d.multiplier d.multiplier_definable d.multiplier_value
  have hpoint := gammaGroundRVSemiringClass_iso (asIso (show P.underlying ⟶ Q.underlying from
    gammaGroundDefinablePointBijection P.underlying.domain Q.underlying.domain p q hP hQ))
  simp only [gammaGroundMeasuredAnnularElement,map_sub,map_add,gammaGroundMeasuredRVForgetRing_class,
    GammaGroundMeasuredRVObject.withZeroForm]
  rw [hA,hpoint,zero_add,sub_self]
end DiamondIntegral.Section3
