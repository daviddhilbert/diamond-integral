import «section 3».GammaGroundGammaSemiring
import «section 3».GammaGroundGammaRVScissors
import «section 3».GammaGroundGammaRVProductLift
import «section 3».GammaGroundRVGradedComparison
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

theorem gammaGroundGammaRVSemiringClass_empty : gammaGroundRVSemiringClass (GammaGroundGammaObject.empty hc ground k).rvLift = 0 := by
  have h := congrArg gammaGroundRVKPlusToSemiring (gammaGroundGammaRVClass_empty (hc := hc) (ground := ground) (k := k))
  simpa only [gammaGroundRVKPlusToSemiring_class, map_zero] using h

theorem gammaGroundGammaRVSemiringClass_unit : gammaGroundRVSemiringClass (GammaGroundGammaObject.unit hc ground).rvLift = 1 := by
  have h := congrArg gammaGroundRVKPlusToSemiring (gammaGroundGammaRVClass_unit (hc := hc) (ground := ground))
  simpa only [gammaGroundRVKPlusToSemiring_class, gammaGroundRVSemiringClass_unit] using h

theorem gammaGroundGammaRVSemiringClass_scissor {A B D E : GammaGroundGammaObject hc ground k} (h : GammaGroundGammaScissor A B D E) :
    gammaGroundRVSemiringClass A.rvLift + gammaGroundRVSemiringClass B.rvLift =
      gammaGroundRVSemiringClass D.rvLift + gammaGroundRVSemiringClass E.rvLift := by
  have hh : gammaGroundGammaClass A + gammaGroundGammaClass B = gammaGroundGammaClass D + gammaGroundGammaClass E :=
    positiveClass_scissor (gammaGroundGammaPresentation hc ground k) h
  have hs := congrArg (gammaGroundRVKPlusToSemiring.comp gammaGroundGammaToRVKPlus) hh
  simpa only [AddMonoidHom.comp_apply, map_add, gammaGroundGammaToRVKPlus_class, gammaGroundRVKPlusToSemiring_class] using hs

def gammaGroundGammaToRVSemiringInvariant :
    PositiveGrothendieck.Invariant (gammaGroundGammaSemiringPresentation hc ground) (R := GammaGroundRVPositiveSemiring (M := M) hc ground) where
  toFun A := gammaGroundRVSemiringClass A.2.rvLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := gammaGroundGammaHom_lift_iso e.hom
    exact gammaGroundRVSemiringClass_iso E
  empty := gammaGroundGammaRVSemiringClass_empty
  unit := gammaGroundGammaRVSemiringClass_unit
  product A B := (gammaGroundRVSemiringClass_iso (asIso (show (A.2.product B.2).rvLift ⟶
    A.2.rvLift.product B.2.rvLift from gammaGroundGammaRVProductBijection A.2 B.2))).trans
      (gammaGroundRVSemiringClass_product A.2.rvLift B.2.rvLift)
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaGroundGammaRVSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [gammaGroundGammaRVSemiringClass_empty, add_zero]

def gammaGroundGammaToRVSemiring : GammaGroundGammaPositiveSemiring hc ground →+* GammaGroundRVPositiveSemiring (M := M) hc ground :=
  PositiveGrothendieck.lift (gammaGroundGammaSemiringPresentation hc ground) gammaGroundGammaToRVSemiringInvariant

@[simp] theorem gammaGroundGammaToRVSemiring_class (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaToRVSemiring (gammaGroundGammaSemiringClass A) = gammaGroundRVSemiringClass A.rvLift :=
  PositiveGrothendieck.lift_of (gammaGroundGammaSemiringPresentation hc ground) gammaGroundGammaToRVSemiringInvariant ⟨k, A⟩

end DiamondIntegral.Section3
