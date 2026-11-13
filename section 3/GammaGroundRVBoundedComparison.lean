import «section 3».GammaGroundRVFiltration
import «section 3».GammaGroundRVGradingConsequences

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundRVBoundedToDirectSum : GammaGroundRVBoundedPositive hc ground k →+ GammaGroundRVDirectSum hc ground :=
  DirectSum.toAddMonoid (fun i => DirectSum.of (GammaGroundRVKPlus hc ground) i.val)

theorem gammaGroundRVBoundedToDirectSum_component (a : GammaGroundRVBoundedPositive hc ground k) (i : Fin (k + 1)) :
    gammaGroundRVBoundedToDirectSum a i.val = a i := by
  induction a using DirectSum.induction_on with
  | zero => rfl
  | of j x =>
    rw [gammaGroundRVBoundedToDirectSum, DirectSum.toAddMonoid_of]
    by_cases he : j = i
    · subst j
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · have hv : i.val ≠ j.val := fun hv => he (Fin.ext hv.symm)
      rw [DirectSum.of_eq_of_ne _ _ _ hv, DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
  | add a b ha hb => rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, ha, hb]

theorem gammaGroundRVBoundedInclude_grading (a : GammaGroundRVBoundedPositive hc ground k) :
    gammaGroundRVPresentationToDirectSum (gammaGroundRVBoundedInclude a) = gammaGroundRVBoundedToDirectSum a := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a =>
    rw [gammaGroundRVBoundedInclude_of, gammaGroundRVPresentationToDirectSum_fixed]
    change DirectSum.of (GammaGroundRVKPlus hc ground) i.val a =
      (DirectSum.toAddMonoid (fun j : Fin (k + 1) => DirectSum.of (GammaGroundRVKPlus hc ground) j.val))
        (DirectSum.of (fun j : Fin (k + 1) => GammaGroundRVKPlus hc ground j.val) i a)
    exact (DirectSum.toAddMonoid_of
      (fun j : Fin (k + 1) => DirectSum.of (GammaGroundRVKPlus hc ground) j.val) i a).symm
  | add a b ha hb =>
    rw [gammaGroundRVBoundedInclude.map_add, gammaGroundRVPresentationToDirectSum.map_add,
      gammaGroundRVBoundedToDirectSum.map_add, ha, hb]

theorem gammaGroundRVBoundedInclude_injective :
    Function.Injective (gammaGroundRVBoundedInclude (hc := hc) (ground := ground) (k := k)) := by
  intro a b hab
  have he := congrArg (gammaGroundRVPresentationToDirectSum (hc := hc) (ground := ground)) hab
  rw [gammaGroundRVBoundedInclude_grading, gammaGroundRVBoundedInclude_grading] at he
  apply DirectSum.ext
  intro i
  have ht := congrArg (fun z : GammaGroundRVDirectSum hc ground => z i.val) he
  simpa only [gammaGroundRVBoundedToDirectSum_component] using ht

end DiamondIntegral.Section3
