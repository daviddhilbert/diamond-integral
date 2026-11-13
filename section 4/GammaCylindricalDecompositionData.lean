import «section 4».GammaCellFormula
import Mathlib.Data.Fintype.EquivFin

/-! Finite actual cylindrical cell decompositions, with disjointness,
coverage and dimensions. Arbitrary finite index families can be reindexed
by Fin without changing the cells; empty and zero-dimensional sets are
handled explicitly. Existence in all dimensions is proved separately. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCylindricalDecompositionData
open GammaOrderLogic GammaCylindricalCells
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Decomposition (B : Base (M := M)) (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) where
  size : ℕ
  pieces : Fin size → Set (Fin n → Values.Gamma (M := M))
  dimension : Fin size → ℕ
  cells : ∀ i, Cell B n (pieces i) (dimension i)
  disjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j))
  cover : X = ⋃ i, pieces i

theorem cell_subset {B : Base (M := M)} {n : ℕ} {X : Set (Fin n → Values.Gamma (M := M))}
    (D : Decomposition B n X) (i : Fin D.size) : D.pieces i ⊆ X := by
  intro x hx
  rw [D.cover]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

def ofFamily {B : Base (M := M)} {n : ℕ} (X : Set (Fin n → Values.Gamma (M := M)))
    {ι : Type*} [Fintype ι] (C : ι → Set (Fin n → Values.Gamma (M := M))) (d : ι → ℕ)
    (hc : ∀ i, Cell B n (C i) (d i)) (hd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : X = ⋃ i, C i) : Decomposition B n X where
  size := Fintype.card ι
  pieces j := C ((Fintype.equivFin ι).symm j)
  dimension j := d ((Fintype.equivFin ι).symm j)
  cells j := hc ((Fintype.equivFin ι).symm j)
  disjoint := by
    intro i j hij
    exact hd (fun he => hij ((Fintype.equivFin ι).symm.injective he))
  cover := by
    ext x
    rw [hcover]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨(Fintype.equivFin ι) i, by simpa only [Equiv.symm_apply_apply] using hi⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨(Fintype.equivFin ι).symm j, hj⟩

def empty (B : Base (M := M)) (n : ℕ) : Decomposition B n ∅ where
  size := 0
  pieces := Fin.elim0
  dimension := Fin.elim0
  cells := by intro i; exact i.elim0
  disjoint := by intro i; exact i.elim0
  cover := by ext x; simp

def zero_univ (B : Base (M := M)) : Decomposition B 0 Set.univ where
  size := 1
  pieces := fun _ => Set.univ
  dimension := fun _ => 0
  cells := fun _ => Cell.base
  disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  cover := by ext x; simp

theorem exists_zero (B : Base (M := M)) (X : Set (Fin 0 → Values.Gamma (M := M))) :
    Nonempty (Decomposition B 0 X) := by
  by_cases he : X = ∅
  · exact he.symm ▸ ⟨empty B 0⟩
  · have hu : X = Set.univ := by
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr he
      apply Set.eq_univ_of_forall
      intro y
      exact (Subsingleton.elim x y) ▸ hx
    exact hu.symm ▸ ⟨zero_univ B⟩

end DiamondIntegral.Section4.GammaCylindricalDecompositionData
