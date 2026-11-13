import «section 4».GammaUnaryDescent

/-! Actual weighted unary Euler pushforward over the original base.
Finite level-set decomposition reduces integer weights to the proved set
image theorem; the actual fibre functions and the total integral are kept
in the conclusion. Higher-dimensional source families are not assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaWeightedPushforward
open GammaOrderLogic GammaDefinableFunctions GammaDefinableEuler GammaEulerSets EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_weighted_image (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (B : Base (M := M)) (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (f : EulerFunction k (PaperGamma (M := M)))
    (hd : IntegerDefinable B (fun x => f (toPaperGamma x)))
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | T (z 0) = z 1}) :
    ∃ P : EulerFunction k (PaperGamma (M := M)),
      IntegerDefinable B (fun y => P (toPaperGamma y)) ∧
      ∃ F : PaperGamma (M := M) → EulerFunction k (PaperGamma (M := M)),
        (∀ y x : Values.Gamma (M := M), F (toPaperGamma y) (toPaperGamma x) =
          if T x = y then f (toPaperGamma x) else 0) ∧
        (∀ y : Values.Gamma (M := M), P (toPaperGamma y) = totalEuler k (F (toPaperGamma y))) ∧
        totalEuler k P = totalEuler k f := by
  let D (n : ℤ) : Set (Values.Gamma (M := M)) := {x | f (toPaperGamma x) = n}
  have hD (n : ℤ) : GammaDefinableOverBase B (D n) := hd.2 n
  have hR (n : ℤ) : GammaDefinable B
      {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D n ∧ T (z 0) = z 1} := by
    exact GammaRelationLogic.inter_definable_base B _ _
      (GammaRelationLogic.preimage_definable_base B _ ((unary_definable_iff B (D n)).mpr (hD n))
        (fun _ : Fin 1 => (0 : Fin 2))) hT
  have hex (n : ℤ) := GammaUnaryDescent.exists_unary_definable_image h00 linear B hΓ k
    (D n) (hD n) T (hR n)
  choose P hdP F hF hP hEuler using hex
  let s := hd.1.toFinset
  let image : EulerFunction k (PaperGamma (M := M)) := ∑ n ∈ s, n • P n
  let fibre (y : PaperGamma (M := M)) : EulerFunction k (PaperGamma (M := M)) :=
    ∑ n ∈ s, n • F n y
  have hwd (n : ℤ) : IntegerDefinable B (fun y => (n • P n) (toPaperGamma y)) := by
    convert (hdP n).map (fun m => n * m) using 1
    funext y
    rw [eval_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id]
  have hid : IntegerDefinable B (fun y => image (toPaperGamma y)) := by
    have h := integerDefinable_finsetSum B s _ (fun n _ => hwd n)
    simpa only [image, eval_finsetSum] using h
  have hfibre (y x : Values.Gamma (M := M)) :
      fibre (toPaperGamma y) (toPaperGamma x) =
        if T x = y then f (toPaperGamma x) else 0 := by
    simp only [fibre, eval_finsetSum, eval_zsmul, hF]
    simp only [zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
    by_cases hy : T x = y
    · simp only [D, Set.mem_ofPred_eq, hy, and_true, ite_true]
      simp_rw [eq_comm (a := f (toPaperGamma x))]
      rw [Finset.sum_ite_eq']
      exact ite_eq_left (hd.1.mem_toFinset.mpr ⟨x, rfl⟩)
    · simp only [hy, and_false, ite_false, Finset.sum_const_zero]
  have hlevels : (∑ n ∈ s, n • indicator h00 B k (D n) (hD n)) = f := by
    apply eval_injective k
    funext x
    obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
    change (∑ n ∈ s, n • indicator h00 B k (D n) (hD n)) (toPaperGamma a) = f (toPaperGamma a)
    simp only [eval_finsetSum, eval_zsmul, indicator_eval]
    simp only [zsmul_eq_mul, Int.cast_id, D, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
    simp_rw [eq_comm (a := f (toPaperGamma a))]
    rw [Finset.sum_ite_eq']
    exact ite_eq_left (hd.1.mem_toFinset.mpr ⟨a, rfl⟩)
  refine ⟨image, hid, fibre, hfibre, ?_, ?_⟩
  · intro y
    simp only [image, fibre, eval_finsetSum, eval_zsmul, map_sum, map_zsmul, hP]
  · simp only [image, map_sum, map_zsmul, hEuler, eulerValue]
    simpa only [map_sum, map_zsmul] using congrArg (totalEuler k) hlevels

end DiamondIntegral.Section4.GammaWeightedPushforward
