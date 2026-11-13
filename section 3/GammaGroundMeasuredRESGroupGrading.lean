import «section 3».GammaGroundMeasuredRESGradedSemiring
import «section 3».GammaGroundMeasuredRVGradingConsequences

/-! The actual graded RES ring and its canonical map into RV. Positive
injectivity is not silently promoted to group-completion injectivity. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

abbrev GammaGroundMeasuredRESGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := RingCompletion (GammaGroundMeasuredRESDirectSum hc ground)

def gammaGroundMeasuredRESGroupDirectSumEquiv : GammaGroundMeasuredRESGrothendieckRing hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRESKPlus hc ground k)) :=
  completionDirectSumEquiv (GammaGroundMeasuredRESKPlus hc ground)

def gammaGroundMeasuredRESRingToRV : GammaGroundMeasuredRESGrothendieckRing hc ground →+* GammaGroundMeasuredRVGrothendieckRing hc ground :=
  Algebra.GrothendieckAddGroup.liftRingHom (Algebra.GrothendieckAddGroup.ofRingHom.comp
    (gammaGroundMeasuredRVDirectSumToPresentation.comp gammaGroundMeasuredRESGradedInclusion))

@[simp] theorem gammaGroundMeasuredRESRingToRV_class (U : GammaGroundMeasuredRESObject hc ground k) :
    gammaGroundMeasuredRESRingToRV (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRESDirectSumClass U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U.obj) := by
  rw [gammaGroundMeasuredRESRingToRV, Algebra.GrothendieckAddGroup.liftRingHom_apply_of]
  change Algebra.GrothendieckAddGroup.of
    (gammaGroundMeasuredRVDirectSumToPresentation (gammaGroundMeasuredRESDirectSumToRV (gammaGroundMeasuredRESDirectSumClass U))) = _
  change Algebra.GrothendieckAddGroup.of
    (gammaGroundMeasuredRVDirectSumToPresentation (DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
      (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) k (gammaGroundMeasuredRESClass U)))) = _
  rw [DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class]
  exact congrArg Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVDirectSumToPresentation_class U.obj)

end DiamondIntegral.Section3
