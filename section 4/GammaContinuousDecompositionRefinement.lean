import «section 4».GammaContinuousPartitions
import «section 4».GammaContinuousStackCells
import «section 4».GammaBoundaryStackCoverage
import «section 4».GammaBoundaryStackDisjointness

/-! Refine each boundary-stack base by a common continuity region and
a continuous cell decomposition of the smaller-arity base. Coverage and
disjointness are proved for the resulting actual continuous cells. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousDecompositionRefinement
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStackCoverage GammaBoundaryStackDisjointness GammaBoundaryStackRefinement
open GammaContinuousCells GammaContinuousPartitions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def refine (h00 : M ⊨ Axioms.ACVF00) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hR : GammaDefinable B R) (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R))
    (Q : CommonCover B n P.size (endpoint P))
    (D : (label : Label P.size) → (j : Q.Index) →
      Decomposition B n (base R P label ∩ Q.domain j)) : Decomposition B (n + 1) R := by
  letI : Finite Q.Index := Q.finite
  letI := Fintype.ofFinite Q.Index
  let piece (p : Σ label : Label P.size, Σ j : Q.Index, Fin (D label j).size) :=
    shape R P p.1 ((D p.1 p.2.1).pieces p.2.2)
  have hbase (label : Label P.size) (j : Q.Index) (i : Fin (D label j).size) :
      (D label j).pieces i ⊆ base R P label ∩ Q.domain j :=
    GammaCylindricalDecompositionData.cell_subset (D label j).toDecomposition i
  refine ofFamily R piece
    (fun p => (D p.1 p.2.1).dimension p.2.2 + dimensionRaise p.1) ?_ ?_ ?_
  · intro p
    exact GammaContinuousStackCells.shape_cell R P p.1 _ ((D p.1 p.2.1).continuous_cells p.2.2)
      (fun _ hx => (hbase _ _ _ hx).1)
      (fun i => (Q.continuous p.2.1 i).mono (fun _ hx => (hbase _ _ _ hx).2))
  · intro p q hpq
    rcases p with ⟨label, j, i⟩
    rcases q with ⟨other, j', i'⟩
    by_cases hl : label = other
    · subst other
      by_cases hj : j = j'
      · subst j'
        have hii' : i ≠ i' := by
          intro he
          apply hpq
          cases he
          rfl
        exact shape_disjoint R P label _ _ ((D label j).disjoint hii')
      · have hd : Disjoint ((D label j).pieces i) ((D label j').pieces i') :=
          (Q.disjoint hj).mono (fun _ hx => (hbase _ _ _ hx).2)
            (fun _ hx => (hbase _ _ _ hx).2)
        exact shape_disjoint R P label _ _ hd
    · have hi : piece ⟨label, j, i⟩ ⊆ stack R P label :=
        shape_mono R P label (fun _ hx => (hbase _ _ _ hx).1)
      have hj : piece ⟨other, j', i'⟩ ⊆ stack R P other :=
        shape_mono R P other (fun _ hx => (hbase _ _ _ hx).1)
      exact (pairwise_disjoint R P hl).mono hi hj
  · ext z
    constructor
    · intro hz
      obtain ⟨label, hl⟩ := cover R P z hz
      obtain ⟨hy, hs⟩ := (mem_shape R P label (base R P label) z).mp hl
      obtain ⟨j, hj⟩ := Q.cover (Fin.tail z)
      have hm : Fin.tail z ∈ ⋃ i, (D label j).pieces i :=
        (D label j).cover ▸ ⟨hy, hj⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
      exact Set.mem_iUnion.mpr ⟨⟨label, j, i⟩, (mem_shape R P label _ z).mpr ⟨hi, hs⟩⟩
    · intro hz
      obtain ⟨⟨label, j, i⟩, hi⟩ := Set.mem_iUnion.mp hz
      exact stack_subset h00 R hR P label
        ((shape_mono R P label (fun _ hx => (hbase _ _ _ hx).1)) hi)

end DiamondIntegral.Section4.GammaContinuousDecompositionRefinement
