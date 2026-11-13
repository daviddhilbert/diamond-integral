import «section 3».CompletionDirectSum
import «section 3».GammaGradedComparison
import «section 3».FiniteGammaGradedComparison
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

def gammaGroupDirectSumEquiv : GammaGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (GammaKGroup hc S) :=
  (ringCompletionCongr (gammaSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (GammaKPlus hc S))

def finiteGammaGroupDirectSumEquiv : FiniteGammaGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (FiniteGammaKPlus hc S k)) :=
  (ringCompletionCongr (finiteGammaSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (FiniteGammaKPlus hc S))

def rvGroupDirectSumEquiv : RVGrothendieckRing (M := M) S ≃+
    DirectSum ℕ (RVKGroup S) :=
  (ringCompletionCongr (rvSemiringEquivDirectSum (M := M) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (RVKPlus S))

def measuredRVGroupDirectSumEquiv : MeasuredRVGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (MeasuredRVKPlus hc S k)) :=
  (ringCompletionCongr (measuredRVSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (MeasuredRVKPlus hc S))

def measuredRESGroupDirectSumEquiv : MeasuredRESGrothendieckRing (M := M) hc S ≃+
    DirectSum ℕ (fun k => Algebra.GrothendieckAddGroup (MeasuredRESKPlus hc S k)) :=
  (ringCompletionCongr (measuredResSemiringEquivDirectSum (hc := hc) (S := S))).toAddEquiv.trans
    (completionDirectSumEquiv (MeasuredRESKPlus hc S))


@[simp] theorem gammaGroupDirectSumEquiv_class {k : ℕ} (A : GammaObject hc S k) :
    gammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (gammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (gammaClass A)) := by
  change completionDirectSumEquiv (GammaKPlus hc S)
    (ringCompletionCongr (gammaSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (gammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (GammaKPlus hc S) k (gammaClass A)

@[simp] theorem finiteGammaGroupDirectSumEquiv_class {k : ℕ} (A : FiniteGammaObject hc S k) :
    finiteGammaGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (finiteGammaSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (FiniteGammaKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (finiteGammaClass A)) := by
  change completionDirectSumEquiv (FiniteGammaKPlus hc S)
    (ringCompletionCongr (finiteGammaSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (finiteGammaSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [finiteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, finiteGammaPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (FiniteGammaKPlus hc S) k (finiteGammaClass A)

@[simp] theorem rvGroupDirectSumEquiv_class {k : ℕ} (A : RVObject S k) :
    rvGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (rvSemiringClass A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (RVKPlus S k)) k
        (Algebra.GrothendieckAddGroup.of (rvClass A)) := by
  change completionDirectSumEquiv (RVKPlus S)
    (ringCompletionCongr (rvSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (rvSemiringClass A))) = _
  rw [ringCompletionCongr_of]
  simp only [rvSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, rvPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (RVKPlus S) k (rvClass A)

@[simp] theorem measuredRVGroupDirectSumEquiv_class {k : ℕ} (A : MeasuredRVObject S k) :
    measuredRVGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (measuredRVSemiringClass hc A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (MeasuredRVKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (measuredRVClass hc A)) := by
  change completionDirectSumEquiv (MeasuredRVKPlus hc S)
    (ringCompletionCongr (measuredRVSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (measuredRVSemiringClass hc A))) = _
  rw [ringCompletionCongr_of]
  simp only [measuredRVSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, measuredRVPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (MeasuredRVKPlus hc S) k (measuredRVClass hc A)

@[simp] theorem measuredRESGroupDirectSumEquiv_class {k : ℕ} (A : MeasuredRESObject S k) :
    measuredRESGroupDirectSumEquiv (Algebra.GrothendieckAddGroup.of (measuredRESSemiringClass hc A)) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (MeasuredRESKPlus hc S k)) k
        (Algebra.GrothendieckAddGroup.of (measuredResClass hc A)) := by
  change completionDirectSumEquiv (MeasuredRESKPlus hc S)
    (ringCompletionCongr (measuredResSemiringEquivDirectSum (S := S)) (Algebra.GrothendieckAddGroup.of (measuredRESSemiringClass hc A))) = _
  rw [ringCompletionCongr_of]
  simp only [measuredResSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, measuredResPresentationToDirectSum_class]
  exact completionDirectSumEquiv_of (MeasuredRESKPlus hc S) k (measuredResClass hc A)
end DiamondIntegral.Section3
