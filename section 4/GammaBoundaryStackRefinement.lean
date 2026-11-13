import «section 4».GammaBoundaryStackFamily
import «section 4».GammaCylindricalCells

/-! Refining the base of a cylindrical boundary stack commutes with
unions and preserves disjointness. A cylindrical cell in the selected
base lifts to an actual cell, with the graph or interval dimension step. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStackRefinement
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStacks GammaBoundaryStackBases GammaCellSections GammaCellUnboundedSections GammaCylindricalCells
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem mem_shape (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    (C : Set (Fin n → Values.Gamma (M := M))) (z : Fin (n + 1) → Values.Gamma (M := M)) :
    z ∈ shape R P label C ↔ Fin.tail z ∈ C ∧ z ∈ shape R P label Set.univ := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u))) <;>
    simp [shape, graphCell, bandCell, upperRayCell, lowerRayCell, lineCell]

theorem shape_iUnion (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    {ι : Type*} (C : ι → Set (Fin n → Values.Gamma (M := M))) :
    shape R P label (⋃ i, C i) = ⋃ i, shape R P label (C i) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hi, hs⟩ := (mem_shape R P label (⋃ i, C i) z).mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, (mem_shape R P label (C i) z).mpr ⟨hi, hs⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hi, hs⟩ := (mem_shape R P label (C i) z).mp hi
    exact (mem_shape R P label (⋃ i, C i) z).mpr ⟨Set.mem_iUnion.mpr ⟨i, hi⟩, hs⟩

theorem shape_disjoint (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    (C D : Set (Fin n → Values.Gamma (M := M))) (hCD : Disjoint C D) :
    Disjoint (shape R P label C) (shape R P label D) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp hCD ((mem_shape R P label C z).mp hz).1 ((mem_shape R P label D z).mp hz').1

theorem shape_cell (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    (C : Set (Fin n → Values.Gamma (M := M))) {d : ℕ} (hc : Cell B n C d)
    (hC : C ⊆ base R P label) : Cell B (n + 1) (shape R P label C) (d + dimensionRaise label) := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · change Cell B (n + 1) (graphCell C (endpoint P i)) (d + 0)
    exact Cell.graph hc _ (shape_definable R P (.inl i) C hc.definable)
  · exact Cell.band hc _ _ (fun y hy => (hC hy).1.2)
      (shape_definable R P (.inr (.inl (i, j))) C hc.definable)
  · exact Cell.upperRay hc _ (shape_definable R P (.inr (.inr (.inl i))) C hc.definable)
  · exact Cell.lowerRay hc _ (shape_definable R P (.inr (.inr (.inr (.inl i)))) C hc.definable)
  · exact Cell.line hc (shape_definable R P (.inr (.inr (.inr (.inr u)))) C hc.definable)

end DiamondIntegral.Section4.GammaBoundaryStackRefinement
