import «section 4».GammaDefinableMaps
import «section 4».GammaQuantifierLogic

/-! Extend an actual definable partial Gamma map by a named constant.
This gives a total original-base map; coefficient weights extended by zero
are unaffected by the choice of its values outside the original domain. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPartialMaps
open GammaOrderLogic GammaRelationLogic

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def extendMap {n : ℕ} (D : Set (Fin n → Values.Gamma (M := M)))
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (c : Values.Gamma (M := M)) (y : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  if y ∈ D then T y else c

theorem extendMap_definable (B : Base (M := M)) {n : ℕ}
    (D : Set (Fin n → Values.Gamma (M := M))) (hD : GammaDefinable B D)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      (fun j => z j.succ) ∈ D ∧ T (fun j => z j.succ) = z 0})
    (c : Values.Gamma (M := M)) (hc : GammaDefinableClosureAtBase B c) :
    GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      extendMap D T c (fun j => z j.succ) = z 0} := by
  have hdomain := preimage_definable_base B D hD (fun j : Fin n => j.succ)
  have hconst : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | c = z 0} := by
    simpa only [GammaDefinableMaps.MapDefinable, eq_comm] using
      GammaDefinableMaps.constant_definable (n := n) B c hc
  have h := GammaQuantifierLogic.union_definable_base B _ _ hT
    (inter_definable_base B _ _ (complement_definable_base B _ hdomain) hconst)
  convert h using 1
  ext z
  change (if (fun j => z j.succ) ∈ D then T (fun j => z j.succ) else c) = z 0 ↔
    (((fun j => z j.succ) ∈ D ∧ T (fun j => z j.succ) = z 0) ∨
      ((fun j => z j.succ) ∉ D ∧ c = z 0))
  by_cases hy : (fun j => z j.succ) ∈ D <;> simp only [hy, ite_true, ite_false,
    not_true_eq_false, not_false_eq_true, true_and, false_and, or_false, false_or]

end DiamondIntegral.Section4.GammaPartialMaps
