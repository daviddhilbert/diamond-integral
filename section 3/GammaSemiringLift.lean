import «section 3».GammaSemiring
import «section 3».GammaRVScissors
import «section 3».GammaRVProductLift
import «section 3».RVGradedComparison

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

theorem gammaRVSemiringClass_empty : rvSemiringClass (GammaObject.empty hc S k).rvLift = 0 := by
  have h := congrArg rvKPlusToSemiring (gammaRVClass_empty (hc := hc) (S := S) (k := k))
  simpa only [rvKPlusToSemiring_class, map_zero] using h

theorem gammaRVSemiringClass_unit : rvSemiringClass (GammaObject.unit hc S).rvLift = 1 := by
  have h := congrArg rvKPlusToSemiring (gammaRVClass_unit (hc := hc) (S := S))
  simpa only [rvKPlusToSemiring_class, rvSemiringClass_unit] using h

theorem gammaRVSemiringClass_scissor {A B D E : GammaObject hc S k} (h : GammaScissor A B D E) :
    rvSemiringClass A.rvLift + rvSemiringClass B.rvLift =
      rvSemiringClass D.rvLift + rvSemiringClass E.rvLift := by
  have hh : gammaClass A + gammaClass B = gammaClass D + gammaClass E :=
    positiveClass_scissor (gammaPresentation hc S k) h
  have hs := congrArg (rvKPlusToSemiring.comp gammaToRVKPlus) hh
  simpa only [AddMonoidHom.comp_apply, map_add, gammaToRVKPlus_class, rvKPlusToSemiring_class] using hs

def gammaToRVSemiringInvariant :
    PositiveGrothendieck.Invariant (gammaSemiringPresentation hc S) (R := RVPositiveSemiring (M := M) S) where
  toFun A := rvSemiringClass A.2.rvLift
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    obtain ⟨E⟩ := gammaHom_lift_iso e.hom
    exact rvSemiringClass_iso E
  empty := gammaRVSemiringClass_empty
  unit := gammaRVSemiringClass_unit
  product A B := (rvSemiringClass_iso (asIso (show (A.2.product B.2).rvLift ⟶
    A.2.rvLift.product B.2.rvLift from gammaRVProductBijection A.2 B.2))).trans
      (rvSemiringClass_product A.2.rvLift B.2.rvLift)
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, rfl, rfl, rfl, rfl⟩ := h
      exact gammaRVSemiringClass_scissor hs
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      simp only [gammaRVSemiringClass_empty, add_zero]

def gammaToRVSemiring : GammaPositiveSemiring hc S →+* RVPositiveSemiring (M := M) S :=
  PositiveGrothendieck.lift (gammaSemiringPresentation hc S) gammaToRVSemiringInvariant

@[simp] theorem gammaToRVSemiring_class (A : GammaObject hc S k) :
    gammaToRVSemiring (gammaSemiringClass A) = rvSemiringClass A.rvLift :=
  PositiveGrothendieck.lift_of (gammaSemiringPresentation hc S) gammaToRVSemiringInvariant ⟨k, A⟩

end DiamondIntegral.Section3
