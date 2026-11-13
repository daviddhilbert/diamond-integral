import «section 3».MeasuredGammaSemiring
import «section 3».MeasuredGammaRVScissors
import «section 3».MeasuredGammaProductLift
import «section 3».MeasuredRVGradedComparison

/-! The actual Gamma lift induces a multiplicative map on the universal
positive semiring, with its prescribed value on every object. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem measuredGammaRVSemiringClass_empty : measuredRVSemiringClass hc (MeasuredGammaObject.empty hc S k).rvLift = 0 := by
  have h := congrArg (measuredRVKPlusToSemiring hc) (measuredGammaRVClass_empty (hc := hc) (S := S) (k := k))
  simpa only [measuredRVKPlusToSemiring_class hc, map_zero] using h

theorem measuredGammaRVSemiringClass_unit : measuredRVSemiringClass hc (MeasuredGammaObject.unit hc S).rvLift = 1 := by
  have h := congrArg (measuredRVKPlusToSemiring hc) (measuredGammaRVClass_unit (hc := hc) (S := S))
  simpa only [measuredRVKPlusToSemiring_class hc, measuredRVSemiringClass_unit hc] using h

theorem measuredGammaRVSemiringClass_scissor {A B D E : MeasuredGammaObject hc S k} (h : MeasuredGammaScissor A B D E) :
    measuredRVSemiringClass hc A.rvLift + measuredRVSemiringClass hc B.rvLift =
      measuredRVSemiringClass hc D.rvLift + measuredRVSemiringClass hc E.rvLift := by
  have hh : measuredGammaClass A + measuredGammaClass B = measuredGammaClass D + measuredGammaClass E :=
    positiveClass_scissor (measuredGammaPresentation hc S k) h
  have hs := congrArg ((measuredRVKPlusToSemiring hc).comp measuredGammaToRVKPlus) hh
  simpa only [AddMonoidHom.comp_apply, map_add, measuredGammaToRVKPlus_class, measuredRVKPlusToSemiring_class hc] using hs

def measuredGammaToRVSemiringInvariant :
    PositiveGrothendieck.Invariant (measuredGammaSemiringPresentation hc S) (R := MeasuredRVPositiveSemiring (M := M) hc S) where
  toFun A := measuredRVSemiringClass hc A.2.rvLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := measuredGammaHom_lift_iso e.hom
    exact measuredRVSemiringClass_iso hc E
  empty := measuredGammaRVSemiringClass_empty
  unit := measuredGammaRVSemiringClass_unit
  product A B := (measuredRVSemiringClass_iso hc (asIso (show (A.2.product B.2).rvLift ⟶
    A.2.rvLift.product hc B.2.rvLift from measuredGammaProductLiftHom A.2 B.2))).trans
      (measuredRVSemiringClass_product hc A.2.rvLift B.2.rvLift)
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact measuredGammaRVSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [measuredGammaRVSemiringClass_empty, add_zero]

def measuredGammaToRVSemiring : MeasuredGammaPositiveSemiring hc S →+* MeasuredRVPositiveSemiring (M := M) hc S :=
  PositiveGrothendieck.lift (measuredGammaSemiringPresentation hc S) measuredGammaToRVSemiringInvariant

@[simp] theorem measuredGammaToRVSemiring_class (A : MeasuredGammaObject hc S k) :
    measuredGammaToRVSemiring (measuredGammaSemiringClass A) = measuredRVSemiringClass hc A.rvLift :=
  PositiveGrothendieck.lift_of (measuredGammaSemiringPresentation hc S) measuredGammaToRVSemiringInvariant ⟨k, A⟩

end DiamondIntegral.Section3
