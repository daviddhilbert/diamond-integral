import «section 4».RVNamedTuples
import «section 4».RVMeasuredIsomorphisms

/-! Adding a named degree-zero tuple on either side gives an actual
original-base measured RV isomorphism. The right-hand product is
explicitly transported back to the original object degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVPointProductIsomorphisms
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVChartDisjointUnion RVNamedTuples
open RVCoordinateMaps RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem product_weight_coordinates {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (u : Fin (b.arity + a.arity) → M) :
    (product a b).correctedWeight u = a.correctedWeight (u ∘ headIndex b.arity a.arity) *
      b.correctedWeight (u ∘ tailIndex b.arity a.arity) :=
  (congrArg (product a b).correctedWeight (join_reconstruct b.arity a.arity u).symm).trans
    (product_weight_join a b _ _)

theorem tuple_weight (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) (u : Fin n → M) :
    (tupleChart B x hx).correctedWeight u = 1 := by
  change 1 * (∏ i : Fin 0, codeValue (Fin.elim0 i)) = 1
  simp

def leftTupleIso (B : Base (M := M)) {n k : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) (a : Chart B k) :
    Iso (product (tupleChart B x hx) a) a := by
  apply coordinateIso _ _ (tailIndex a.arity n)
  · refine ⟨(fun _ hu => hu.2), ?_, ?_⟩
    · intro u hu v hv he
      have hh : u ∘ headIndex a.arity n = v ∘ headIndex a.arity n := hu.1.trans hv.1.symm
      exact (join_reconstruct a.arity n u).symm.trans
        ((congrArg₂ (join a.arity n) hh he).trans (join_reconstruct a.arity n v))
    · intro y hy
      refine ⟨join a.arity n x y, (productSet_join _ _ _ _).mpr ⟨Set.mem_singleton _, hy⟩, ?_⟩
      exact funext (join_tail a.arity n x y)
  · intro u _
    exact (product_weight_coordinates (tupleChart B x hx) a u).trans
      ((congrArg (fun z => z * a.correctedWeight (u ∘ tailIndex a.arity n)) (tuple_weight B x hx _)).trans (one_mul _))

def rightRawData {B : Base (M := M)} {n k : ℕ} (a : Chart B k) (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Data B (n + a.arity) (0 + k) :=
  ofChart (product a (tupleChart B x hx))

def rightData {B : Base (M := M)} {n k : ℕ} (a : Chart B k) (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Data B (n + a.arity) k :=
  castGrade (Nat.zero_add k) (rightRawData a x hx)

theorem castGrade_weight {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) (u : Fin n → M) :
    (castGrade h a).toChart.correctedWeight u = a.toChart.correctedWeight u := by
  cases h
  rfl

def rightTupleIso {B : Base (M := M)} {n k : ℕ} (a : Chart B k) (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Iso (rightData a x hx).toChart a := by
  have hd : (rightData a x hx).domain = (product a (tupleChart B x hx)).domain :=
    castGrade_domain (Nat.zero_add k) (rightRawData a x hx)
  apply coordinateIso _ _ (headIndex n a.arity)
  · refine ⟨?_, ?_, ?_⟩
    · intro u hu
      change u ∈ (rightData a x hx).domain at hu
      rw [hd] at hu
      exact hu.1
    · intro u hu v hv he
      change u ∈ (rightData a x hx).domain at hu
      change v ∈ (rightData a x hx).domain at hv
      rw [hd] at hu hv
      have ht : u ∘ tailIndex n a.arity = v ∘ tailIndex n a.arity := hu.2.trans hv.2.symm
      exact (join_reconstruct n a.arity u).symm.trans
        ((congrArg₂ (join n a.arity) he ht).trans (join_reconstruct n a.arity v))
    · intro y hy
      refine ⟨join n a.arity y x, ?_, funext (join_head n a.arity y x)⟩
      change join n a.arity y x ∈ (rightData a x hx).domain
      rw [hd]
      exact (productSet_join _ _ _ _).mpr ⟨hy, Set.mem_singleton _⟩
  · intro u _
    let v : Fin (n + a.arity) → M := u
    change (rightData a x hx).toChart.correctedWeight v = a.correctedWeight (v ∘ headIndex n a.arity)
    have hw : (rightData a x hx).toChart.correctedWeight v = (product a (tupleChart B x hx)).correctedWeight v :=
      castGrade_weight (Nat.zero_add k) (rightRawData a x hx) v
    exact hw.trans ((product_weight_coordinates a (tupleChart B x hx) v).trans
      ((congrArg (a.correctedWeight (v ∘ headIndex n a.arity) * ·)
        (tuple_weight B x hx (v ∘ tailIndex n a.arity))).trans (mul_one _)))

end DiamondIntegral.Section4.RVPointProductIsomorphisms
