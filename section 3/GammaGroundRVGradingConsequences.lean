import «section 3».GammaGroundRVGradedComparison
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

theorem gammaGroundRVPresentationToDirectSum_fixed (a : GammaGroundRVKPlus hc ground k) :
    gammaGroundRVPresentationToDirectSum (gammaGroundRVKPlusToSemiring a) = DirectSum.of (GammaGroundRVKPlus hc ground) k a := by
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  rw [gammaGroundRVKPlusToSemiring_class, gammaGroundRVPresentationToDirectSum_class]
  rfl

theorem gammaGroundRVKPlusToSemiring_injective :
    Function.Injective (gammaGroundRVKPlusToSemiring (hc := hc) (ground := ground) (k := k)) := by
  intro a b hab
  have he := congrArg (gammaGroundRVPresentationToDirectSum (hc := hc) (ground := ground)) hab
  rw [gammaGroundRVPresentationToDirectSum_fixed, gammaGroundRVPresentationToDirectSum_fixed] at he
  have ht := congrArg (fun z : GammaGroundRVDirectSum hc ground => z k) he
  simpa only [DirectSum.of_eq_same] using ht

def gammaGroundRVGroupDirectSumEquiv : GammaGroundRVGrothendieckRing hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundRVKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundRVSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundRVKPlus hc ground))

@[simp] theorem gammaGroundRVGroupDirectSumEquiv_class (U : GammaGroundRVObject hc ground k) :
    gammaGroundRVGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass U)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundRVKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundRVClass U)) := by
  change completionDirectSumEquiv (GammaGroundRVKPlus hc ground)
    (ringCompletionCongr (gammaGroundRVSemiringEquivDirectSum (hc := hc) (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundRVSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundRVSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundRVPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass U)

end DiamondIntegral.Section3
