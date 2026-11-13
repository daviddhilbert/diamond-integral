import «section 3».GammaGroundMeasuredRVSemiring
import «section 3».GammaGroundRVSemiring
import «section 3».CompletionTensor
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def gammaGroundMeasuredRVForgetInvariant :
    PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc B)
      (R := GammaGroundRVPositiveSemiring hc B) where
  toFun U := gammaGroundRVSemiringClass U.2.underlying
  iso := by
    rintro A D ⟨k,U,V,⟨e⟩,rfl,rfl⟩
    exact gammaGroundRVSemiringClass_iso (asIso (show U.underlying ⟶ V.underlying from e.hom.bijection))
  empty := gammaGroundRVSemiringClass_empty
  unit := gammaGroundRVSemiringClass_unit
  product U V := gammaGroundRVSemiringClass_product U.2.underlying V.2.underlying
  scissor := by
    intro A D E F h
    rcases h with ⟨k,U,V,W,X,hs,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩
    · obtain ⟨Z,Y,hY,hU,hV,hW,hX⟩ := hs
      apply gammaGroundRVSemiringClass_scissor
      refine ⟨Z.underlying,Y,hY,?_,?_,?_,?_⟩
      · exact congrArg GammaGroundMeasuredRVObject.underlying hU
      · exact congrArg GammaGroundMeasuredRVObject.underlying hV
      · exact congrArg GammaGroundMeasuredRVObject.underlying hW
      · exact congrArg GammaGroundMeasuredRVObject.underlying hX
    · simp only [GammaGroundMeasuredRVObject.empty,gammaGroundRVSemiringClass_empty,add_zero]

/-- Forgetting forms is a genuine homomorphism of positive semirings,
with the original ground and all actual RV domains retained. -/
def gammaGroundMeasuredRVForgetSemiring :
    GammaGroundMeasuredRVPositiveSemiring hc B →+* GammaGroundRVPositiveSemiring hc B :=
  PositiveGrothendieck.lift (gammaGroundMeasuredRVSemiringPresentation hc B)
    (gammaGroundMeasuredRVForgetInvariant (hc := hc) (B := B))

@[simp] theorem gammaGroundMeasuredRVForgetSemiring_class {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B k) :
    gammaGroundMeasuredRVForgetSemiring (gammaGroundMeasuredRVSemiringClass U) =
      gammaGroundRVSemiringClass U.underlying :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc B)
    (gammaGroundMeasuredRVForgetInvariant (hc := hc) (B := B)) ⟨k,U⟩

/-- Additive completion is used only after the positive forgetful map
has been constructed and checked on every actual object. -/
def gammaGroundMeasuredRVForgetRing :
    GammaGroundMeasuredRVGrothendieckRing hc B →+* GammaGroundRVGrothendieckRing hc B :=
  ringCompletionMap gammaGroundMeasuredRVForgetSemiring
@[simp] theorem gammaGroundMeasuredRVForgetRing_class {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B k) :
    gammaGroundMeasuredRVForgetRing (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass U.underlying) := by
  rw [gammaGroundMeasuredRVForgetRing,ringCompletionMap_of,gammaGroundMeasuredRVForgetSemiring_class]

end DiamondIntegral.Section3
