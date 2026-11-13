import «section 4».Section3GammaCodeBridge
import «section 4».FiniteTupleGraphProduct
import «section 3».GammaGroundGammaProducts

/-! Definable binary Gamma relations commute with the explicit
concatenation convention used by chart graphs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaRelationBridge
open GammaOrderLogic Section3GammaCodeBridge FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def splitMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n m : ℕ) :
    Map (DefSet.univ ((volumeGammaSpace hc).power (Fin (m + n))) S)
      (DefSet.univ (((volumeGammaSpace hc).power (Fin n)).prod ((volumeGammaSpace hc).power (Fin m))) S) :=
  ((universalPowerProjection (volumeGammaSpace hc) S (headIndex m n)).pair
    (universalPowerProjection (volumeGammaSpace hc) S (tailIndex m n))).corestrict (fun _ => Set.mem_univ _)

def mergeIndices (n m : ℕ) : Fin (m + n) → Fin (n + m) :=
  join m n (Fin.castAdd m) (Fin.natAdd n)

theorem append_mergeIndices {α : Type*} (n m : ℕ) (x : Fin n → α) (y : Fin m → α) :
    Fin.append x y ∘ mergeIndices n m = join m n x y := by
  apply FiniteTupleGraphProduct.block_ext m n
  · funext i
    simp only [Function.comp_apply, mergeIndices, join_head, Fin.append_left]
  · funext i
    simp only [Function.comp_apply, mergeIndices, join_tail, Fin.append_right]

def mergeMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n m : ℕ) :
    Map (DefSet.univ (((volumeGammaSpace hc).power (Fin n)).prod ((volumeGammaSpace hc).power (Fin m))) S)
      (DefSet.univ ((volumeGammaSpace hc).power (Fin (m + n))) S) :=
  (universalPowerProjection (volumeGammaSpace hc) S (mergeIndices n m)).comp
    ((gammaAppendMap (DefSet.univ ((volumeGammaSpace hc).power (Fin n)) S)
      (DefSet.univ ((volumeGammaSpace hc).power (Fin m)) S)).comp
        ((universalProductFst _ _ S).pair (universalProductSnd _ _ S)))

theorem mergeMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (n m : ℕ)
    (a : DefSet.univ (((volumeGammaSpace hc).power (Fin n)).prod ((volumeGammaSpace hc).power (Fin m))) S) :
    (mergeMap hc S n m a).val = join m n a.val.1 a.val.2 := append_mergeIndices n m a.val.1 a.val.2

theorem relation_iff {n m : ℕ} (R : (Fin n → Values.Gamma (M := M)) → (Fin m → Values.Gamma (M := M)) → Prop) :
    GammaGroundRelationDefinable hc B ((volumeGammaSpace hc).power (Fin n)) ((volumeGammaSpace hc).power (Fin m)) R ↔
      GammaDefinable B {z : Fin (m + n) → Values.Gamma (M := M) |
        R (z ∘ headIndex m n) (z ∘ tailIndex m n)} := by
  constructor
  · intro h
    exact (native_iff _).mp (h.preimage (splitMap hc B.real n m))
  · intro h
    have hh := ((native_iff (hc := hc) _).mpr h).preimage (mergeMap hc B.real n m)
    apply hh.congr
    intro z
    change R ((mergeMap hc B.real n m ⟨z, Set.mem_univ _⟩).val ∘ headIndex m n)
      ((mergeMap hc B.real n m ⟨z, Set.mem_univ _⟩).val ∘ tailIndex m n) ↔ R z.1 z.2
    rw [mergeMap_value]
    simp only [Function.comp_def, join_head, join_tail]

end DiamondIntegral.Section4.Section3GammaRelationBridge
