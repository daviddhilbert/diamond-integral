import «section 3».CompletionDirectSum
import «section 3».CompletionEquivalences
import «section 3».GammaGroundGammaGradedComparison
import «section 3».GammaGroundFiniteGammaGradedComparison
import «section 3».GammaGroundMeasuredGammaGradedComparison
import «section 3».GammaGroundMeasuredFiniteGammaGradedComparison
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundGammaGroupDirectSumEquiv : GammaGroundGammaGrothendieckRing (M := M) hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundGammaKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundGammaSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundGammaKPlus hc ground))

@[simp] theorem gammaGroundGammaGroupDirectSumEquiv_class {k : ℕ} (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundGammaKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundGammaClass A)) := by
  change completionDirectSumEquiv (GammaGroundGammaKPlus hc ground)
    (ringCompletionCongr (gammaGroundGammaSemiringEquivDirectSum (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass A)

def gammaGroundFiniteGammaGroupDirectSumEquiv : GammaGroundFiniteGammaGrothendieckRing (M := M) hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundFiniteGammaKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundFiniteGammaKPlus hc ground))

@[simp] theorem gammaGroundFiniteGammaGroupDirectSumEquiv_class {k : ℕ} (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundFiniteGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundFiniteGammaKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundFiniteGammaClass A)) := by
  change completionDirectSumEquiv (GammaGroundFiniteGammaKPlus hc ground)
    (ringCompletionCongr (gammaGroundFiniteGammaSemiringEquivDirectSum (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundFiniteGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundFiniteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundFiniteGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass A)

def gammaGroundMeasuredGammaGroupDirectSumEquiv : GammaGroundMeasuredGammaGrothendieckRing (M := M) hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredGammaKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundMeasuredGammaSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundMeasuredGammaKPlus hc ground))

@[simp] theorem gammaGroundMeasuredGammaGroupDirectSumEquiv_class {k : ℕ} (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredGammaKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredGammaClass A)) := by
  change completionDirectSumEquiv (GammaGroundMeasuredGammaKPlus hc ground)
    (ringCompletionCongr (gammaGroundMeasuredGammaSemiringEquivDirectSum (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass A)

def gammaGroundMeasuredFiniteGammaGroupDirectSumEquiv : GammaGroundMeasuredFiniteGammaGrothendieckRing (M := M) hc ground ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredFiniteGammaKPlus hc ground k)) :=
  (ringCompletionCongr (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := ground))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaGroundMeasuredFiniteGammaKPlus hc ground))

@[simp] theorem gammaGroundMeasuredFiniteGammaGroupDirectSumEquiv_class {k : ℕ} (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredFiniteGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredFiniteGammaKPlus hc ground k)) k
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredFiniteGammaClass A)) := by
  change completionDirectSumEquiv (GammaGroundMeasuredFiniteGammaKPlus hc ground)
    (ringCompletionCongr (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (ground := ground))
      (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredFiniteGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass A)

end DiamondIntegral.Section3
