import «section 4».GammaContinuousCells
import «section 4».GammaBoundaryStackRefinement

/-! A continuous base cell lifts through a boundary stack whenever its
active endpoint functions are continuous on that base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousStackCells
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStacks GammaBoundaryStackBases GammaCellSections GammaCellUnboundedSections GammaContinuousCells
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem shape_cell {B : Base (M := M)} {n d : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    (C : Set (Fin n → Values.Gamma (M := M))) (hc : Cell B n C d)
    (hC : C ⊆ base R P label) (hT : ∀ i, ContinuousOn (endpoint P i) C) :
    Cell B (n + 1) (shape R P label C) (d + dimensionRaise label) := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · exact Cell.graph hc _ (hT i) (shape_definable R P (.inl i) C hc.definable)
  · exact Cell.band hc _ _ (hT i) (hT j) (fun y hy => (hC hy).1.2)
      (shape_definable R P (.inr (.inl (i, j))) C hc.definable)
  · exact Cell.upperRay hc _ (hT i)
      (shape_definable R P (.inr (.inr (.inl i))) C hc.definable)
  · exact Cell.lowerRay hc _ (hT i)
      (shape_definable R P (.inr (.inr (.inr (.inl i)))) C hc.definable)
  · exact Cell.line hc (shape_definable R P (.inr (.inr (.inr (.inr u)))) C hc.definable)

end DiamondIntegral.Section4.GammaContinuousStackCells
