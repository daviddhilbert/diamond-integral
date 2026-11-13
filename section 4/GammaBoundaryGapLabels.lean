import «section 4».GammaBoundaryStackFamily
import «section 4».OrderGapComponents

/-! Non-point boundary stacks are labelled by optional lower and upper
endpoints. Their active endpoint domains and absence of boundary points
make them valid ordered gaps in each actual fibre. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryGapLabels
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStacks GammaBoundaryStackBases GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

abbrev GapLabel (N : ℕ) := Option (Fin N) × Option (Fin N)
def gapLabel {N : ℕ} : GapLabel N → Label N
  | (some i, some j) => .inr (.inl (i, j))
  | (some i, none) => .inr (.inr (.inl i))
  | (none, some j) => .inr (.inr (.inr (.inl j)))
  | (none, none) => .inr (.inr (.inr (.inr ())))

def gapSource (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) : GapLabel P.size → Set (Fin n → Values.Gamma (M := M))
  | (some i, some j) => P.domain i ∩ P.domain j
  | (some i, none) => P.domain i
  | (none, some j) => P.domain j
  | (none, none) => Set.univ

theorem gapSource_iff (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (y : Fin n → Values.Gamma (M := M)) : y ∈ gapSource R P q ↔
      (∀ i, q.1 = some i → y ∈ P.domain i) ∧ (∀ j, q.2 = some j → y ∈ P.domain j) := by
  rcases q with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp [gapSource]

theorem shape_eq_gap (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (C : Set (Fin n → Values.Gamma (M := M))) : shape R P (gapLabel q) C =
      {z : Fin (n + 1) → Values.Gamma (M := M) | Fin.tail z ∈ C ∧ z 0 ∈ OrderGapComponents.gap
        (q.1.map (fun i => endpoint P i (Fin.tail z))) (q.2.map (fun i => endpoint P i (Fin.tail z)))} := by
  rcases q with ⟨lo, hi⟩
  cases lo <;> cases hi <;> ext z <;>
    simp [shape, gapLabel, graphCell, bandCell, upperRayCell, lowerRayCell, lineCell,
      OrderGapComponents.gap, OrderGapComponents.LowerBound, OrderGapComponents.UpperBound]

theorem base_source (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ base R P (gapLabel q)) : y ∈ gapSource R P q := by
  rcases q with ⟨lo, hi⟩
  cases lo <;> cases hi
  · exact Set.mem_univ y
  · exact hy.1
  · exact hy.1
  · exact hy.1.1

theorem base_active (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ base R P (gapLabel q)) :
    y ∈ activeBase R (shape R P (gapLabel q) (gapSource R P q)) := by
  rcases q with ⟨lo, hi⟩
  cases lo <;> cases hi <;> exact hy.2

theorem valid_gap (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ base R P (gapLabel q)) :
    OrderGapComponents.Valid {x | Fin.cons x y ∈ GammaFamilyBoundary.Boundary R}
      (q.1.map (fun i => endpoint P i y)) (q.2.map (fun i => endpoint P i y)) := by
  have hs := (gapSource_iff R P q y).mp (base_source R P q y hy)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    cases he : q.1 with
    | none => simp only [he, Option.map_none, reduceCtorEq] at ha
    | some i =>
      have hval : endpoint P i y = a := by simpa only [he, Option.map_some, Option.some.injEq] using ha
      exact hval ▸ endpoint_mem P i y (hs.1 i he)
  · intro a ha
    cases he : q.2 with
    | none => simp only [he, Option.map_none, reduceCtorEq] at ha
    | some i =>
      have hval : endpoint P i y = a := by simpa only [he, Option.map_some, Option.some.injEq] using ha
      exact hval ▸ endpoint_mem P i y (hs.2 i he)
  · intro x hx hgap
    have hS : Fin.cons x y ∈ shape R P (gapLabel q) (gapSource R P q) := by
      rw [shape_eq_gap]
      exact ⟨base_source R P q y hy, hgap⟩
    exact ((mem_activeBase R _ y).mp (base_active R P q y hy)).2 x hS hx

theorem stack_gap (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (q : GapLabel P.size)
    (z : Fin (n + 1) → Values.Gamma (M := M)) (hz : z ∈ stack R P (gapLabel q)) :
    Fin.tail z ∈ base R P (gapLabel q) ∧ z 0 ∈ OrderGapComponents.gap
      (q.1.map (fun i => endpoint P i (Fin.tail z))) (q.2.map (fun i => endpoint P i (Fin.tail z))) := by
  change z ∈ shape R P (gapLabel q) (base R P (gapLabel q)) at hz
  rw [shape_eq_gap] at hz
  exact hz

end DiamondIntegral.Section4.GammaBoundaryGapLabels
