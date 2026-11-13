import «section 4».GammaCylindricalDecompositionData
import «section 4».GammaBoundaryStackCoverage
import «section 4».GammaBoundaryStackDisjointness
import «section 4».GammaBoundaryStackRefinement

/-! Every original-base definable Gamma set has a finite decomposition
into the project's actual cylindrical graph/band/ray/line cells. Boundary
functions and all base refinements stay over that original base. These
cells do not stipulate continuous endpoints; continuity and topological
dimension identification are separate assertions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCylindricalDecompositionExistence
open GammaOrderLogic GammaFiniteGraphPartition GammaBoundaryStackFamily GammaCylindricalCells
open GammaBoundaryStackCoverage GammaBoundaryStackDisjointness GammaBoundaryStackRefinement GammaCylindricalDecompositionData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def refine (h00 : M ⊨ Axioms.ACVF00) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hR : GammaDefinable B R) (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R))
    (D : (label : Label P.size) → Decomposition B n (base R P label)) : Decomposition B (n + 1) R :=
  ofFamily R
    (fun p : Σ label : Label P.size, Fin (D label).size => shape R P p.1 ((D p.1).pieces p.2))
    (fun p => (D p.1).dimension p.2 + dimensionRaise p.1)
    (fun p => shape_cell R P p.1 _ ((D p.1).cells p.2) (cell_subset (D p.1) p.2))
    (by
      intro p q hpq
      rcases p with ⟨label, i⟩
      rcases q with ⟨other, j⟩
      by_cases he : label = other
      · subst other
        have hij : i ≠ j := by
          intro h
          apply hpq
          cases h
          rfl
        exact shape_disjoint R P label _ _ ((D label).disjoint hij)
      · have hi : shape R P label ((D label).pieces i) ⊆ stack R P label :=
          shape_mono R P label (cell_subset (D label) i)
        have hj : shape R P other ((D other).pieces j) ⊆ stack R P other :=
          shape_mono R P other (cell_subset (D other) j)
        exact (pairwise_disjoint R P he).mono hi hj)
    (by
      ext z
      constructor
      · intro hz
        obtain ⟨label, hl⟩ := cover R P z hz
        change z ∈ shape R P label (base R P label) at hl
        rw [(D label).cover, shape_iUnion] at hl
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hl
        exact Set.mem_iUnion.mpr ⟨⟨label, i⟩, hi⟩
      · intro hz
        obtain ⟨⟨label, i⟩, hi⟩ := Set.mem_iUnion.mp hz
        exact stack_subset h00 R hR P label ((shape_mono R P label (cell_subset (D label) i)) hi))

theorem exists_decomposition (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X) :
    Nonempty (Decomposition B n X) := by
  induction n with
  | zero => exact exists_zero B X
  | succ n ih =>
    obtain ⟨P⟩ := GammaFiniteGraphPartition.exists_boundaryPartition h00 hκ hs B hr hγ X hX
    let D (label : Label P.size) : Decomposition B n (base X P label) :=
      Classical.choice (ih (base X P label) (base_definable X hX P label))
    exact ⟨refine h00 X hX P D⟩

end DiamondIntegral.Section4.GammaCylindricalDecompositionExistence
