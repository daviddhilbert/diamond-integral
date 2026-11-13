import «section 3».CompletionDirectSum
import «section 3».MeasuredGammaGradedComparison
import «section 3».MeasuredFiniteGammaGradedComparison
import «section 3».RVGradedComparison
import «section 3».MeasuredRVGradedComparison
import «section 3».MeasuredRESGradedComparison
import «section 3».CompletionEquivalences

/-! The groupified graded presentations retain exactly their individual
homogeneous Grothendieck groups. These are additive comparisons. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredGammaGroupDirectSumEquiv : MeasuredGammaGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (MeasuredGammaKGroup hc S) :=
  (ringCompletionCongr (measuredGammaSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (MeasuredGammaKPlus hc S))

def measuredFiniteGammaGroupDirectSumEquiv : MeasuredFiniteGammaGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (MeasuredFiniteGammaKPlus hc S k)) :=
  (ringCompletionCongr (measuredFiniteGammaSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (MeasuredFiniteGammaKPlus hc S))

@[simp] theorem measuredGammaGroupDirectSumEquiv_class {k : ℕ} (A : MeasuredGammaObject hc S k) :
    measuredGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (measuredGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (MeasuredGammaKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (measuredGammaClass A)) := by
  change completionDirectSumEquiv (MeasuredGammaKPlus hc S)
    (ringCompletionCongr (measuredGammaSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (measuredGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [measuredGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, measuredGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (MeasuredGammaKPlus hc S) k (measuredGammaClass A)

@[simp] theorem measuredFiniteGammaGroupDirectSumEquiv_class {k : ℕ} (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (measuredFiniteGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (MeasuredFiniteGammaKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (measuredFiniteGammaClass A)) := by
  change completionDirectSumEquiv (MeasuredFiniteGammaKPlus hc S)
    (ringCompletionCongr (measuredFiniteGammaSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (measuredFiniteGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [measuredFiniteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, measuredFiniteGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass A)


end DiamondIntegral.Section3
