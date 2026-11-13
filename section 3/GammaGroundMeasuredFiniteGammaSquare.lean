import «section 3».GammaGroundMeasuredFiniteGammaScissors
import «section 3».GammaGroundMeasuredGammaRVScissors
import «section 3».GammaGroundMeasuredRESPositiveComparison
/-! The actual measured finite-Gamma/RES/Gamma/RV square commutes on
fixed-degree positive classes. No quotient by an integration relation is used. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundMeasuredFiniteGammaToRESKPlus : GammaGroundMeasuredFiniteGammaKPlus hc ground k →+ GammaGroundMeasuredRESKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaPresentation hc ground k) {
    toFun A := gammaGroundMeasuredRESClass A.resLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := gammaGroundMeasuredFiniteGammaHom_lift_iso e.hom
      exact gammaGroundMeasuredRESClass_iso E
    empty := by
      apply gammaGroundMeasuredRESToRVKPlus_injective
      rw [gammaGroundMeasuredRESToRVKPlus_class, map_zero]
      exact gammaGroundMeasuredGammaRVClass_empty
    scissor := by
      intro A B D E h
      apply gammaGroundMeasuredRESToRVKPlus_injective
      simp only [map_add, gammaGroundMeasuredRESToRVKPlus_class]
      change gammaGroundMeasuredRVClass A.obj.rvLift + gammaGroundMeasuredRVClass B.obj.rvLift =
        gammaGroundMeasuredRVClass D.obj.rvLift + gammaGroundMeasuredRVClass E.obj.rvLift
      have hs0 : gammaGroundMeasuredGammaClass A.obj + gammaGroundMeasuredGammaClass B.obj =
          gammaGroundMeasuredGammaClass D.obj + gammaGroundMeasuredGammaClass E.obj :=
        positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) h
      have hs := congrArg gammaGroundMeasuredGammaToRVKPlus hs0
      simpa only [map_add, gammaGroundMeasuredGammaToRVKPlus_class] using hs }

@[simp] theorem gammaGroundMeasuredFiniteGammaToRESKPlus_class (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaToRESKPlus (gammaGroundMeasuredFiniteGammaClass A) = gammaGroundMeasuredRESClass A.resLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem gammaGroundMeasuredFiniteGamma_positive_square :
    (gammaGroundMeasuredRESToRVKPlus (M := M) (ground := ground) (k := k)).comp (gammaGroundMeasuredFiniteGammaToRESKPlus (hc := hc)) =
      gammaGroundMeasuredGammaToRVKPlus.comp gammaGroundMeasuredFiniteGammaToGammaKPlus := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredFiniteGammaPresentation hc ground k)
  intro A
  change gammaGroundMeasuredRESToRVKPlus (gammaGroundMeasuredFiniteGammaToRESKPlus (gammaGroundMeasuredFiniteGammaClass A)) =
    gammaGroundMeasuredGammaToRVKPlus (gammaGroundMeasuredFiniteGammaToGammaKPlus (gammaGroundMeasuredFiniteGammaClass A))
  rw [gammaGroundMeasuredFiniteGammaToRESKPlus_class, gammaGroundMeasuredRESToRVKPlus_class,
    gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredGammaToRVKPlus_class]
  rfl

end DiamondIntegral.Section3
