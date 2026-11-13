import «section 4».GammaFamilySlicesTwo
import «section 4».FiniteTupleBlocks

/-! Arbitrary finite Gamma slices after naming precisely the fixed suffix.
The coordinate image uses an injection, preserving every RV code. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBlockSlices
open GammaOrderLogic GammaRelationLogic GammaQuantifierLogic GammaBaseExtension GammaFamilyIntegration
open FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem slice_definable_base (B : Base (M := M)) (n m : ℕ)
    (R : Set (Fin (n + m) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (y : Fin n → Values.Gamma (M := M)) :
    GammaDefinable (withGamma B (Set.range y)) {u | join n m u y ∈ R} := by
  let B' := withGamma B (Set.range y)
  have hfix (i : Fin n) : GammaDefinable B'
      {z : Fin (n + m) → Values.Gamma (M := M) | z (tailIndex n m i) = y i} :=
    preimage_definable_base B' _ ((unary_definable_iff B' {y i}).mpr
      (gammaName_extend B (Set.range y) (y i) (Set.mem_range_self i)))
      (fun _ : Fin 1 => tailIndex n m i)
  have hA := inter_definable_base B' R _ (gammaRelation_extend B (Set.range y) hR)
    (finite_iInter_definable_base B' _ hfix)
  have h := image_definable_base B' _ hA (headIndex n m) (headIndex_injective n m)
  convert h using 1
  ext u
  change join n m u y ∈ R ↔
    ∃ z ∈ R ∩ (⋂ i : Fin n, {z | z (tailIndex n m i) = y i}), z ∘ headIndex n m = u
  constructor
  · intro hu
    refine ⟨join n m u y, ⟨hu, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq, join_tail, implies_true]
    · funext i
      exact join_head n m u y i
  · rintro ⟨z, ⟨hzR, hz⟩, he⟩
    have ht : z ∘ tailIndex n m = y := by
      funext i
      exact Set.mem_iInter.mp hz i
    have hez : join n m u y = z := by
      rw [← he, ← ht]
      exact join_reconstruct n m z
    rwa [hez]

def slice {n m : ℕ} (f : (Fin (n + m) → Values.Gamma (M := M)) → ℤ)
    (y : Fin n → Values.Gamma (M := M)) (u : Fin m → Values.Gamma (M := M)) : ℤ :=
  f (join n m u y)

theorem slice_definable (B : Base (M := M)) (n m : ℕ)
    (f : (Fin (n + m) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    IntegerFamilyDefinable (withGamma B (Set.range y)) (slice f y) := by
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro a ⟨u, rfl⟩
    exact ⟨join n m u y, rfl⟩
  · intro a
    exact slice_definable_base B n m {z | f z = a} (hf.2 a) y

end DiamondIntegral.Section4.GammaBlockSlices
