import «section 3».FiniteColumnPartition
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
set_option autoImplicit false
open Classical
noncomputable section
namespace DiamondIntegral.Section3
variable {X Y : Type}

/-- Finitely many columns and finite rows force a finite nonempty-column
projection. Empty columns cause no finiteness assertion about the domain. -/
theorem finite_projection_of_finite_columns (R : Y → X → Prop) (A : Set X)
    (hc : (relationColumn R '' A).Finite)
    (hr : ∀ y, {x | x ∈ A ∧ R y x}.Finite) : {x | x ∈ A ∧ ∃ y, R y x}.Finite := by
  classical
  let C := relationColumn R '' A
  letI := hc.fintype
  let U (c : C) : Set X := if h : c.val.Nonempty then {x | x ∈ A ∧ R h.choose x} else ∅
  have hU : ∀ c, (U c).Finite := by
    intro c
    dsimp only [U]
    split_ifs with h
    · exact hr h.choose
    · exact Set.finite_empty
  apply (Set.finite_iUnion hU).subset
  rintro x ⟨hx,y,hy⟩
  let c : C := ⟨relationColumn R x,⟨x,hx,rfl⟩⟩
  have hne : c.val.Nonempty := ⟨y,hy⟩
  apply Set.mem_iUnion.mpr
  refine ⟨c,?_⟩
  change x ∈ U c
  dsimp only [U]
  rw [dif_pos hne]
  exact ⟨hx,hne.choose_spec⟩
end DiamondIntegral.Section3
