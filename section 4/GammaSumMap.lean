import «section 4».GammaProductFamilies
import «section 4».GammaDefinableMaps
import «section 4».GammaWeightProfiles

/-! Actual product-volume and corrected-weight maps on two coordinate
blocks. Native Gamma multiplication is the manuscript's addition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSumMap
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem graph_of_mapDefinable (B : Base (M := M)) {n : ℕ}
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hT : MapDefinable B T) :
    GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)} := by
  unfold MapDefinable at hT
  convert hT using 1
  ext z
  change z 0 = T (Fin.tail z) ↔ z 0 = T (fun i => z i.succ)
  have he : Fin.tail z = (fun i => z i.succ) := by funext i; rfl
  rw [he]

def sumMap {n m : ℕ}
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin (n + m) → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  T (z ∘ headIndex n m) * U (z ∘ tailIndex n m)

theorem sumMap_definable (B : Base (M := M)) {n m : ℕ}
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) (hU : MapDefinable B U) : MapDefinable B (sumMap T U) :=
  mul_definable B _ _ (GammaDefinableMaps.reindex_definable B T hT (headIndex n m))
    (GammaDefinableMaps.reindex_definable B U hU (tailIndex n m))

theorem sumMap_join {n m : ℕ}
    (T : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (u : Fin m → Values.Gamma (M := M)) (y : Fin n → Values.Gamma (M := M)) :
    sumMap T U (join n m u y) = T u * U y := by
  have hh : join n m u y ∘ headIndex n m = u := funext (join_head n m u y)
  have ht : join n m u y ∘ tailIndex n m = y := funext (join_tail n m u y)
  change T (join n m u y ∘ headIndex n m) * U (join n m u y ∘ tailIndex n m) = _
  rw [hh, ht]

theorem prod_blocks {A : Type*} [CommMonoid A] (n m : ℕ) (z : Fin (n + m) → A) :
    (∏ i, z i) = (∏ i, z (headIndex n m i)) * (∏ i, z (tailIndex n m i)) := by
  induction m with
  | zero => simp [headIndex, tailIndex]
  | succ m ih =>
    have hl : (∏ i, z i) = z 0 * (∏ i : Fin (n + m), z i.succ) := Fin.prod_univ_succ z
    have hr : (∏ i, z (headIndex n (m + 1) i)) =
        z 0 * (∏ i : Fin m, z (headIndex n m i).succ) := by
      rw [Fin.prod_univ_succ]
      rfl
    have hi := ih (Fin.tail z)
    change (∏ i : Fin (n + m), z i.succ) =
      (∏ i, z (headIndex n m i).succ) * (∏ i, z (tailIndex n m i).succ) at hi
    calc
      _ = z 0 * (∏ i : Fin (n + m), z i.succ) := hl
      _ = z 0 * ((∏ i, z (headIndex n m i).succ) * (∏ i, z (tailIndex n m i).succ)) :=
        congrArg (fun a => z 0 * a) hi
      _ = (z 0 * (∏ i, z (headIndex n m i).succ)) * (∏ i, z (tailIndex n m i).succ) :=
        (mul_assoc _ _ _).symm
      _ = _ := by rw [hr]; rfl

theorem correctedWeight_sumMap {n m : ℕ}
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    correctedWeight (sumMap μ σ) = sumMap (correctedWeight μ) (correctedWeight σ) := by
  funext z
  change (μ (z ∘ headIndex n m) * σ (z ∘ tailIndex n m)) * (∏ i, z i) =
    (μ (z ∘ headIndex n m) * (∏ i, z (headIndex n m i))) *
      (σ (z ∘ tailIndex n m) * (∏ i, z (tailIndex n m i)))
  rw [prod_blocks]
  ac_rfl

end DiamondIntegral.Section4.GammaSumMap
