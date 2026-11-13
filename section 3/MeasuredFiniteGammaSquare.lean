import «section 3».MeasuredFiniteGammaScissors
import «section 3».MeasuredGammaRVScissors
import «section 3».MeasuredRESPositiveComparison

/-! The actual measured finite-Gamma/RES/Gamma/RV square commutes on
fixed-degree positive classes. No quotient by an integration relation is used. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def measuredFiniteGammaToRESKPlus : MeasuredFiniteGammaKPlus hc S k →+ MeasuredRESKPlus hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredFiniteGammaPresentation hc S k) {
    toFun A := measuredResClass hc A.resLift
    iso := fun h => by
      obtain ⟨e⟩ := h
      obtain ⟨E⟩ := measuredFiniteGammaHom_lift_iso e.hom
      exact measuredResClass_iso hc E
    empty := by
      apply measuredResToRVKPlus_injective hc
      rw [measuredResToRVKPlus_class, map_zero]
      exact measuredGammaRVClass_empty
    scissor := by
      intro A B D E h
      apply measuredResToRVKPlus_injective hc
      simp only [map_add, measuredResToRVKPlus_class]
      change measuredRVClass hc A.obj.rvLift + measuredRVClass hc B.obj.rvLift =
        measuredRVClass hc D.obj.rvLift + measuredRVClass hc E.obj.rvLift
      have hs0 : measuredGammaClass A.obj + measuredGammaClass B.obj =
          measuredGammaClass D.obj + measuredGammaClass E.obj :=
        positiveClass_scissor (measuredGammaPresentation hc S k) h
      have hs := congrArg measuredGammaToRVKPlus hs0
      simpa only [map_add, measuredGammaToRVKPlus_class] using hs }

@[simp] theorem measuredFiniteGammaToRESKPlus_class (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaToRESKPlus (measuredFiniteGammaClass A) = measuredResClass hc A.resLift :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem measuredFiniteGamma_positive_square :
    (measuredResToRVKPlus (M := M) (S := S) (k := k) hc).comp (measuredFiniteGammaToRESKPlus (hc := hc)) =
      measuredGammaToRVKPlus.comp measuredFiniteGammaToGammaKPlus := by
  apply PositiveAdditiveGrothendieck.hom_ext (measuredFiniteGammaPresentation hc S k)
  intro A
  change measuredResToRVKPlus hc (measuredFiniteGammaToRESKPlus (measuredFiniteGammaClass A)) =
    measuredGammaToRVKPlus (measuredFiniteGammaToGammaKPlus (measuredFiniteGammaClass A))
  rw [measuredFiniteGammaToRESKPlus_class, measuredResToRVKPlus_class,
    measuredFiniteGammaToGammaKPlus_class, measuredGammaToRVKPlus_class]
  rfl

end DiamondIntegral.Section3
