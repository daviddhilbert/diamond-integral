import «section 3».GammaGroundRESGradedSemiring
import «section 3».GammaGroundRVGradingConsequences

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

abbrev GammaGroundRESGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := RingCompletion (GammaGroundRESDirectSum hc ground)

def gammaGroundRESGroupDirectSumEquiv : GammaGroundRESGrothendieckRing hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundRESKPlus hc ground k)) :=
  completionDirectSumEquiv (GammaGroundRESKPlus hc ground)

def gammaGroundRESRingToRV : GammaGroundRESGrothendieckRing hc ground →+* GammaGroundRVGrothendieckRing hc ground :=
  Algebra.GrothendieckAddGroup.liftRingHom (Algebra.GrothendieckAddGroup.ofRingHom.comp
    (gammaGroundRVDirectSumToPresentation.comp gammaGroundRESGradedInclusion))

@[simp] theorem gammaGroundRESRingToRV_class (U : GammaGroundRESObject hc ground k) :
    gammaGroundRESRingToRV (Algebra.GrothendieckAddGroup.of (gammaGroundRESDirectSumClass U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass U.obj) := by
  rw [gammaGroundRESRingToRV, Algebra.GrothendieckAddGroup.liftRingHom_apply_of]
  change Algebra.GrothendieckAddGroup.of
    (gammaGroundRVDirectSumToPresentation (gammaGroundRESDirectSumToRV (gammaGroundRESDirectSumClass U))) = _
  change Algebra.GrothendieckAddGroup.of
    (gammaGroundRVDirectSumToPresentation (DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
      (DirectSum.of (GammaGroundRESKPlus hc ground) k (gammaGroundRESClass U)))) = _
  rw [DirectSum.map_of, gammaGroundRESToRVKPlus_class]
  exact congrArg Algebra.GrothendieckAddGroup.of (gammaGroundRVDirectSumToPresentation_class U.obj)

end DiamondIntegral.Section3
