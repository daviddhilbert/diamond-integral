import «section 3».GammaGroundAnnularForgetting
import «section 3».GammaGroundUnmeasuredTensorMap
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

structure GammaGroundAnnularGenerator (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) where
  radius : GammaGroundAnnularRadius hc B
  positivePoint : GammaGroundMeasuredRVObject hc B 1
  unitPoint : GammaGroundMeasuredRVObject hc B 1
  positiveMember : positivePoint.underlying.domain
  unitMember : unitPoint.underlying.domain
  positive_singleton : ∀ x : positivePoint.underlying.domain, x = positiveMember
  unit_singleton : ∀ x : unitPoint.underlying.domain, x = unitMember

def GammaGroundAnnularGenerator.element (d : GammaGroundAnnularGenerator hc B) :
    GammaGroundMeasuredRVGrothendieckRing hc B :=
  gammaGroundMeasuredAnnularElement d.radius d.positivePoint d.unitPoint

def gammaGroundAnnularIdeal : Ideal (GammaGroundMeasuredRVGrothendieckRing hc B) :=
  Ideal.span (Set.range (GammaGroundAnnularGenerator.element (hc := hc) (B := B)))

/-- All coefficients and all choices of stipulated annular generators
are killed by the genuine unmeasured forgetful ring map. -/
theorem gammaGroundAnnularIdeal_le_forget_kernel :
    gammaGroundAnnularIdeal (hc := hc) (B := B) ≤ RingHom.ker gammaGroundMeasuredRVForgetRing := by
  apply Ideal.span_le.mpr
  rintro x ⟨d,rfl⟩
  exact gammaGroundMeasuredAnnularElement_forget_zero d.radius d.positivePoint d.unitPoint
    d.positiveMember d.unitMember d.positive_singleton d.unit_singleton

/-- Every commuting presentation, including a bounded presentation
once its concrete maps are constructed, sends the full annular pullback
into the actual unmeasured tensor kernel. No surjective section is chosen. -/
theorem gammaGroundAnnularPullback_le_actual_tensor_kernel
    {T : Type*} [CommRing T]
    (q : T →+* GammaGroundMeasuredRVGrothendieckRing hc B)
    (f : T →+* (RingCompletion (GammaGroundRESDirectSum hc B) ⊗[GammaGroundFiniteGammaGrothendieckRing hc B]
      GammaGroundGammaGrothendieckRing hc B))
    (hcomm : gammaGroundUnmeasuredGroupTensorMap.comp f = gammaGroundMeasuredRVForgetRing.comp q) :
    Ideal.comap q (gammaGroundAnnularIdeal (hc := hc) (B := B)) ≤
      Ideal.comap f (RingHom.ker gammaGroundUnmeasuredGroupTensorMap) := by
  exact ideal_pullback_le_kernel q (gammaGroundUnmeasuredGroupTensorMap.comp f)
    gammaGroundMeasuredRVForgetRing hcomm gammaGroundAnnularIdeal gammaGroundAnnularIdeal_le_forget_kernel
end DiamondIntegral.Section3
