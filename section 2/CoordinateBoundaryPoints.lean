import «section 2».RVFibrePoints
import «section 2».AtomicPolydiscs

/-! Pointwise witnesses for uniform boundary representatives. The base
contains exactly the other VF coordinates and the boundary RV tag. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawCoordinateSection {n : ℕ} (A : Set (Fin (n+1) → M)) (i : Fin (n+1))
    (a : Fin n → M) : Set M := {x | Fin.insertNth i x a ∈ A}

theorem tupleBase_snoc_rv (B : ParameterBase M) {n : ℕ} (a : Fin n → M) (t : RVInfinity M) :
    tupleBase B (Fin.snoc a t.val) = adjoinRV (tupleBase B a) t := by
  simp only [tupleBase,adjoinRV,Fin.range_snoc,Set.union_insert]

theorem coordinate_boundary_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) {n : ℕ} (A : Set (Fin (n+1) → M))
    (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (i : Fin (n+1)) (a : Fin n → M) (ha : ∀ j, iVF (a j))
    (t : RVInfinity M) (ht : t ∈ scalarRVBoundary (rawCoordinateSection A i a)) :
    ∃ x ∈ rvRawFibre t, GammaParameters.DefinableClosureAtBase
      (tupleBase B (Fin.snoc a t.val)) .vf x := by
  have hsection := coordinate_section_definable B i a ha A hA
  have hpoint := boundary_rv_fibre_definable_point h00 (tupleBase B a)
    (rawCoordinateSection A i a) hsection t ht
  rwa [← tupleBase_snoc_rv] at hpoint

end DiamondIntegral.Section2
