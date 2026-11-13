import «section 3».GammaGroundGammaRESLift
import «section 3».GammaGroundGammaRVScissors
import «section 3».GammaGroundRESPositiveComparison
import «section 3».GammaGroundFiniteGammaScissors
/-! Fixed-degree finite Gamma scissors and the actual commutative square
of positive additive maps to Gamma, RES and RV. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundFiniteGammaToRESKPlus : GammaGroundFiniteGammaKPlus hc ground k →+ GammaGroundRESKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundFiniteGammaPresentation hc ground k) {
    toFun A := gammaGroundRESClass A.resLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := gammaGroundFiniteGammaHom_lift_iso e.hom
      exact gammaGroundRESClass_iso E
    empty := by
      apply gammaGroundRESToRVKPlus_injective
      rw [gammaGroundRESToRVKPlus_class, map_zero]
      exact gammaGroundGammaRVClass_empty
    scissor := by
      intro A B D E h
      apply gammaGroundRESToRVKPlus_injective
      simp only [map_add, gammaGroundRESToRVKPlus_class]
      change gammaGroundRVClass A.obj.rvLift + gammaGroundRVClass B.obj.rvLift = gammaGroundRVClass D.obj.rvLift + gammaGroundRVClass E.obj.rvLift
      have hs0 : gammaGroundGammaClass A.obj + gammaGroundGammaClass B.obj = gammaGroundGammaClass D.obj + gammaGroundGammaClass E.obj :=
        positiveClass_scissor (gammaGroundGammaPresentation hc ground k) h
      have hs := congrArg gammaGroundGammaToRVKPlus hs0
      simpa only [map_add, gammaGroundGammaToRVKPlus_class] using hs }

@[simp] theorem gammaGroundFiniteGammaToRESKPlus_class (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaToRESKPlus (gammaGroundFiniteGammaClass A) = gammaGroundRESClass A.resLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem gammaGroundFiniteGamma_positive_square :
    (gammaGroundRESToRVKPlus (M := M) (ground := ground) (k := k)).comp (gammaGroundFiniteGammaToRESKPlus (hc := hc)) =
      gammaGroundGammaToRVKPlus.comp gammaGroundFiniteGammaToGammaKPlus := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundFiniteGammaPresentation hc ground k)
  intro A
  change gammaGroundRESToRVKPlus (gammaGroundFiniteGammaToRESKPlus (gammaGroundFiniteGammaClass A)) =
    gammaGroundGammaToRVKPlus (gammaGroundFiniteGammaToGammaKPlus (gammaGroundFiniteGammaClass A))
  rw [gammaGroundFiniteGammaToRESKPlus_class, gammaGroundRESToRVKPlus_class,
    gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundGammaToRVKPlus_class]
  rfl

end DiamondIntegral.Section3
