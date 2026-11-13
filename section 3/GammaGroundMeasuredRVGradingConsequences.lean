import «section 3».GammaGroundMeasuredRVGradedComparison
import «section 3».CompletionDirectSum
import «section 3».CompletionEquivalences
import «section 3».PresentationHomExt

/-! Actual fixed-degree inclusions and group gradings after the checked
Gamma-ground RV semiring/direct-sum comparison. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRVPresentationToDirectSum_fixed (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVKPlusToSemiring a) = DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k a := by
  obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
  rw [gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVPresentationToDirectSum_class]
  rfl

theorem gammaGroundMeasuredRVKPlusToSemiring_injective :
    Function.Injective (gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := ground) (k := k)) := by
  intro a b hab
  have he := congrArg (gammaGroundMeasuredRVPresentationToDirectSum (hc := hc) (ground := ground)) hab
  rw [gammaGroundMeasuredRVPresentationToDirectSum_fixed, gammaGroundMeasuredRVPresentationToDirectSum_fixed] at he
  have ht := congrArg (fun z : GammaGroundMeasuredRVDirectSum hc ground => z k) he
  simpa only [DirectSum.of_eq_same] using ht

def gammaGroundMeasuredRVGroupDirectSumEquiv : GammaGroundMeasuredRVGrothendieckRing hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundMeasuredRVSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundMeasuredRVKPlus hc ground))

@[simp] theorem gammaGroundMeasuredRVGroupDirectSumEquiv_class (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVClass U)) := by
  change completionDirectSumEquiv (GammaGroundMeasuredRVKPlus hc ground)
    (ringCompletionCongr (gammaGroundMeasuredRVSemiringEquivDirectSum (hc := hc) (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredRVSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredRVPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass U)

end DiamondIntegral.Section3
