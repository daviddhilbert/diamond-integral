import «section 4».GammaRationalAffineContinuity
import «section 4».GammaCylindricalCellGeometry
import «section 4».GammaCylindricalDecompositionData

/-! Classical cylindrical cells with continuous endpoint functions.
Forgetting continuity gives the already checked Euler cell witnesses;
their recursive dimensions and Euler values are unchanged. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DiamondIntegral.Section4.GammaTopology

namespace DiamondIntegral.Section4.GammaContinuousCells
open GammaOrderLogic GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive Cell (B : Base (M := M)) :
    (n : ℕ) → Set (Fin n → Values.Gamma (M := M)) → ℕ → Prop where
  | base : Cell B 0 Set.univ 0
  | graph {n d C} (hc : Cell B n C d)
      (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hT : ContinuousOn T C) (hR : GammaDefinable B (graphCell C T)) :
      Cell B (n + 1) (graphCell C T) d
  | band {n d C} (hc : Cell B n C d)
      (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hl : ContinuousOn l C) (hu : ContinuousOn u C)
      (hlu : ∀ y ∈ C, l y < u y) (hR : GammaDefinable B (bandCell C l u)) :
      Cell B (n + 1) (bandCell C l u) (d + 1)
  | upperRay {n d C} (hc : Cell B n C d)
      (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hl : ContinuousOn l C) (hR : GammaDefinable B (upperRayCell C l)) :
      Cell B (n + 1) (upperRayCell C l) (d + 1)
  | lowerRay {n d C} (hc : Cell B n C d)
      (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hu : ContinuousOn u C) (hR : GammaDefinable B (lowerRayCell C u)) :
      Cell B (n + 1) (lowerRayCell C u) (d + 1)
  | line {n d C} (hc : Cell B n C d) (hR : GammaDefinable B (lineCell C)) :
      Cell B (n + 1) (lineCell C) (d + 1)

theorem Cell.cylindrical {B : Base (M := M)} {n d : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} (hc : Cell B n C d) :
    GammaCylindricalCells.Cell B n C d := by
  induction hc with
  | base => exact .base
  | graph _ T _ hR ih => exact .graph ih T hR
  | band _ l u _ _ hlu hR ih => exact .band ih l u hlu hR
  | upperRay _ l _ hR ih => exact .upperRay ih l hR
  | lowerRay _ u _ hR ih => exact .lowerRay ih u hR
  | line _ hR ih => exact .line ih hR

theorem Cell.definable {B : Base (M := M)} {n d : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} (hc : Cell B n C d) : GammaDefinable B C :=
  hc.cylindrical.definable

theorem Cell.nonempty {B : Base (M := M)} {n d : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} (hc : Cell B n C d) : C.Nonempty :=
  GammaCylindricalCellGeometry.nonempty hc.cylindrical

theorem Cell.dimension_le {B : Base (M := M)} {n d : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} (hc : Cell B n C d) : d ≤ n :=
  GammaCylindricalCellGeometry.dimension_le hc.cylindrical

structure Decomposition (B : Base (M := M)) (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) extends
    GammaCylindricalDecompositionData.Decomposition B n X where
  continuous_cells : ∀ i, Cell B n (pieces i) (dimension i)

def ofFamily {B : Base (M := M)} {n : ℕ} (X : Set (Fin n → Values.Gamma (M := M)))
    {ι : Type*} [Fintype ι] (C : ι → Set (Fin n → Values.Gamma (M := M))) (d : ι → ℕ)
    (hc : ∀ i, Cell B n (C i) (d i)) (hd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : X = ⋃ i, C i) : Decomposition B n X where
  toDecomposition := GammaCylindricalDecompositionData.ofFamily X C d (fun i => (hc i).cylindrical) hd hcover
  continuous_cells j := hc ((Fintype.equivFin ι).symm j)

def empty (B : Base (M := M)) (n : ℕ) : Decomposition B n ∅ where
  toDecomposition := GammaCylindricalDecompositionData.empty B n
  continuous_cells i := i.elim0

def zero_univ (B : Base (M := M)) : Decomposition B 0 Set.univ where
  toDecomposition := GammaCylindricalDecompositionData.zero_univ B
  continuous_cells _ := .base

theorem exists_zero (B : Base (M := M)) (X : Set (Fin 0 → Values.Gamma (M := M))) :
    Nonempty (Decomposition B 0 X) := by
  by_cases he : X = ∅
  · exact he.symm ▸ ⟨empty B 0⟩
  · have hu : X = Set.univ := by
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr he
      exact Set.eq_univ_of_forall (fun y => (Subsingleton.elim x y) ▸ hx)
    exact hu.symm ▸ ⟨zero_univ B⟩

end DiamondIntegral.Section4.GammaContinuousCells
