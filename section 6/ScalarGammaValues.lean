import «section 6».GammaMapArithmetic

/-! Actual Gamma values of a definable VF scalar, with value one at
zero. The real-code map uses rv(1) at zero, so every target code is
proper and the entire graph stays over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def scalarGammaValueMap (S : Set M) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ (rawGammaPresentation (M := M)) S) := by
  let P := rawVFSpace (M := M) 1
  let f (x : Fin 1 → VF M) : Gamma M :=
    GammaParameters.codeValue (iRv (if x 0 = 0 then (1 : VF M) else x 0).val)
  let F (z : Fin 1 → M) : Fin 1 → M := fun _ => iRv (if z 0 = iVFZero then iVFOne else z 0)
  have hz : S.DefinableFun LRV (fun _ : Fin 1 → M => iVFZero) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
      (show S.DefinableMap LRV (fun _ : Fin 1 → M => Fin.elim0) from fun j => j.elim0)
  have ho : S.DefinableFun LRV (fun _ : Fin 1 → M => iVFOne) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfOne)).comp
      (show S.DefinableMap LRV (fun _ : Fin 1 → M => Fin.elim0) from fun j => j.elim0)
  have hIf : S.DefinableFun LRV (fun z : Fin 1 → M => if z 0 = iVFZero then iVFOne else z 0) :=
    Set.DefinableFun.ite ((Set.DefinableFun.proj LRV).ofPred_eq hz) ho (Set.DefinableFun.proj LRV)
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![if z 0 = iVFZero then iVFOne else z 0]) from
        fun j => by fin_cases j; exact hIf)
  have hCode (c : P.domain) : F c.val (0 : Fin 1) =
      iRv (if (P.decode c) 0 = 0 then (1 : VF M) else (P.decode c) 0).val := by
    have hc := congrFun (vfValues_decode c) 0
    change ((P.decode c) 0).val = c.val (0 : Fin 1) at hc
    have hzero : c.val (0 : Fin 1) = iVFZero ↔ (P.decode c) 0 = 0 := by
      rw [← hc]
      change ((P.decode c) 0).val = (0 : VF M).val ↔ (P.decode c) 0 = 0
      exact Subtype.val_inj
    by_cases hx : (P.decode c) 0 = 0
    · simp only [F,if_pos hx,if_pos (hzero.mpr hx)]
      rfl
    · simp only [F,if_neg hx,if_neg (fun h => hx (hzero.mp h)),hc]
  have hdom (c : P.domain) : F c.val ∈ (rawGammaPresentation (M := M)).domain := by
    change GammaParameters.NonzeroRV (F c.val (0 : Fin 1))
    rw [hCode c]
    let y : VF M := if (P.decode c) 0 = 0 then 1 else (P.decode c) 0
    have hy : y ≠ 0 := by
      dsimp only [y]
      split_ifs with h
      · exact one_ne_zero
      · exact h
    exact ⟨(rv M y).property,fun he => hy ((CanonicalRV.encodedRv_zero_iff y).mp he)⟩
  refine Map.ofCodes (DefSet.univ P S) f F hF hdom ?_
  intro c
  change GammaParameters.codeValue (F c.val (0 : Fin 1)) = f (P.decode c)
  rw [hCode c]

theorem scalarGammaValueMap_nonzero (S : Set M) (x : Fin 1 → VF M) (hx : x 0 ≠ 0) :
    ((scalarGammaValueMap S ⟨x,Set.mem_univ _⟩).val : Gamma M).val = vfValue (x 0) := by
  change (GammaParameters.codeValue (iRv (if x 0 = 0 then (1 : VF M) else x 0).val)).val = _
  rw [if_neg hx]
  exact nonzero_rv_codeValue_val (rv M (x 0)) (fun he => hx ((rv_eq_zero_iff _).mp he))

end DiamondIntegral.Section6
