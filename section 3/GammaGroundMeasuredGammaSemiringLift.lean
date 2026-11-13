import «section 3».GammaGroundMeasuredGammaSemiring
import «section 3».GammaGroundMeasuredGammaRVScissors
import «section 3».GammaGroundMeasuredGammaProductLift
import «section 3».GammaGroundMeasuredRVGradedComparison
/-! The actual Gamma lift induces a multiplicative map on the universal
positive semiring, with its prescribed value on every object. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredGammaRVSemiringClass_empty : gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredGammaObject.empty hc ground k).rvLift = 0 := by
  have h := congrArg (gammaGroundMeasuredRVKPlusToSemiring) (gammaGroundMeasuredGammaRVClass_empty (hc := hc) (ground := ground) (k := k))
  simpa only [gammaGroundMeasuredRVKPlusToSemiring_class, map_zero] using h

theorem gammaGroundMeasuredGammaRVSemiringClass_unit : gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredGammaObject.unit hc ground).rvLift = 1 := by
  have h := congrArg (gammaGroundMeasuredRVKPlusToSemiring) (gammaGroundMeasuredGammaRVClass_unit (hc := hc) (ground := ground))
  simpa only [gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVSemiringClass_unit] using h

theorem gammaGroundMeasuredGammaRVSemiringClass_scissor {A B D E : GammaGroundMeasuredGammaObject hc ground k} (h : GammaGroundMeasuredGammaScissor A B D E) :
    gammaGroundMeasuredRVSemiringClass A.rvLift + gammaGroundMeasuredRVSemiringClass B.rvLift =
      gammaGroundMeasuredRVSemiringClass D.rvLift + gammaGroundMeasuredRVSemiringClass E.rvLift := by
  have hh : gammaGroundMeasuredGammaClass A + gammaGroundMeasuredGammaClass B = gammaGroundMeasuredGammaClass D + gammaGroundMeasuredGammaClass E :=
    positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) h
  have hs := congrArg ((gammaGroundMeasuredRVKPlusToSemiring).comp gammaGroundMeasuredGammaToRVKPlus) hh
  simpa only [AddMonoidHom.comp_apply, map_add, gammaGroundMeasuredGammaToRVKPlus_class, gammaGroundMeasuredRVKPlusToSemiring_class] using hs

def gammaGroundMeasuredGammaToRVSemiringInvariant :
    PositiveGrothendieck.Invariant (gammaGroundMeasuredGammaSemiringPresentation hc ground) (R := GammaGroundMeasuredRVPositiveSemiring (M := M) hc ground) where
  toFun A := gammaGroundMeasuredRVSemiringClass A.2.rvLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := gammaGroundMeasuredGammaHom_lift_iso e.hom
    exact gammaGroundMeasuredRVSemiringClass_iso E
  empty := gammaGroundMeasuredGammaRVSemiringClass_empty
  unit := gammaGroundMeasuredGammaRVSemiringClass_unit
  product A B := (gammaGroundMeasuredRVSemiringClass_iso (asIso (show (A.2.product B.2).rvLift ⟶
    A.2.rvLift.product B.2.rvLift from gammaGroundMeasuredGammaProductLiftHom A.2 B.2))).trans
      (gammaGroundMeasuredRVSemiringClass_product A.2.rvLift B.2.rvLift)
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaGroundMeasuredGammaRVSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [gammaGroundMeasuredGammaRVSemiringClass_empty, add_zero]

def gammaGroundMeasuredGammaToRVSemiring : GammaGroundMeasuredGammaPositiveSemiring hc ground →+* GammaGroundMeasuredRVPositiveSemiring (M := M) hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredGammaSemiringPresentation hc ground) gammaGroundMeasuredGammaToRVSemiringInvariant

@[simp] theorem gammaGroundMeasuredGammaToRVSemiring_class (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaToRVSemiring (gammaGroundMeasuredGammaSemiringClass A) = gammaGroundMeasuredRVSemiringClass A.rvLift :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredGammaSemiringPresentation hc ground) gammaGroundMeasuredGammaToRVSemiringInvariant ⟨k, A⟩

end DiamondIntegral.Section3
