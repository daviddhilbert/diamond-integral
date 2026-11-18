import «section 3».GammaBasicConeNonzero
import IntegrationSection6.ElementaryProductCoordinates
import IntegrationSection6.GammaWeightDecomposition

/-! For a full-weight source the full-weight part of an elementary
blowup is exactly its nonzero-parameter part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem elementary_fullWeight_pair_iff
    (U : SpecialTransformations.Section4.RVObject (M := M) S (n+1)) (i : Fin (n+1))
    (hU : ∀ u : U.domain, ∀ j, U.value u j ≠ 0)
    (u : U.domain) (s : positiveRV (M := M) S) :
    ¬ (rvPackPair U.domain (positiveRV S) u s).val ∈
      (rvLowDomain (IntegrationInACVF.Section6.elementary U i)).carrier ↔ s.val 0 ≠ 0 := by
  let a : (IntegrationInACVF.Section6.elementary U i).domain := rvPackPair U.domain (positiveRV S) u s
  change ¬ a.val ∈ (rvLowDomain (IntegrationInACVF.Section6.elementary U i)).carrier ↔ _
  rw [mem_rvLowDomain,rvWeight_le_pred_iff_zero]
  have ha : (IntegrationInACVF.Section6.elementary U i).value a = blowupValue i (U.value u) (s.val 0) := by
    rw [elementary_value,elementaryProjection_pair,elementaryParameter_pair]
  rw [ha]
  constructor
  · intro h hs
    apply h
    refine ⟨i,?_⟩
    rw [blowupValue_same,hs,zero_mul,RVOperations.zero_val]
  · intro hs ⟨j,hj⟩
    have hz : blowupValue i (U.value u) (s.val 0) j = 0 :=
      Subtype.ext (hj.trans RVOperations.zero_val.symm)
    by_cases hji : j = i
    · subst j
      rw [blowupValue_same] at hz
      exact (mul_ne_zero hs (hU u i)) hz
    · rw [blowupValue_other i _ _ j hji] at hz
      exact hU u j hz

end DiamondIntegral.Section3
