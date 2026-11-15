import IntegrationSection5.CellCentreGeometry
import IntegrationSection5.VFPermutation

/-! Actual horizontal strips and swapped vertical strips of 2-cells. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section4.BalancedFibres
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

def swappedCell (R : Set (VF (M := M) × VF (M := M))) : Set (VF (M := M) × VF (M := M)) :=
  {p | Prod.swap p ∈ R}

theorem swapped_cell_vertical_strip (h : CellData R f t) :
    swappedCell R = {p | p.2 ∈ first R ∧ rv (p.1-f p.2) = t} := by
  ext p
  constructor
  · intro hp
    have ha : p.2 ∈ first R := ⟨Prod.swap p,hp,rfl⟩
    exact ⟨ha,(Set.ext_iff.mp (h.fibres p.2 ha) p.1).mp hp⟩
  · rintro ⟨ha,hb⟩
    exact (Set.ext_iff.mp (h.fibres p.2 ha) p.1).mpr hb

theorem balanced_cell_horizontal_strip (hb : IsBalanced R f r t) :
    R = {p | p.2 ∈ second R ∧ rv (p.1-positionInverse hb.2.2.1.bijective p.2) = r} := by
  ext p
  have hRow := balanced_horizontal_fibre hb.2.2.1 hb.1 p.2
  constructor
  · intro hp
    have hE := (hb.2.2.1.subset hp).2
    exact ⟨hE,(Set.ext_iff.mp (hRow hE) p.1).mp hp⟩
  · rintro ⟨hE,hx⟩
    exact (Set.ext_iff.mp (hRow hE) p.1).mpr hx

theorem graph_cell_horizontal_strip (h : CellData R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) :
    R = {p | p.2 ∈ second R ∧
      rv (p.1-positionInverse (zero_paradigm_position_bijective h ht hi) p.2) = rv (0 : VF (M := M))} := by
  let H := zero_paradigm_position_bijective h ht hi
  have hGraph := graph_of_zero_paradigm h ht
  ext p
  constructor
  · intro hp
    have hg := (Set.ext_iff.mp hGraph p).mp hp
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    rw [hg.2,positionInverse_left H p.1 hg.1,sub_self]
  · rintro ⟨hE,hx⟩
    have hpEq : p.1 = positionInverse H p.2 := sub_eq_zero.mp ((rv_eq_zero_iff _).mp hx)
    apply (Set.ext_iff.mp hGraph p).mpr
    refine ⟨hpEq ▸ positionInverse_mem H p.2 hE,?_⟩
    exact ((congrArg f hpEq).trans (positionInverse_right H p.2 hE)).symm

theorem swapped_cell_gamma (hR : GammaSetDefinable G (cellPointSet R)) :
    GammaSetDefinable G (cellPointSet (swappedCell R)) := by
  let σ := Equiv.swap (0 : Fin 2) 1
  let U := PresentedSet.univ (pointSpace (M := M) 2 0) G.real
  have h := (gammaLogicInput G).preimage_real (vfPermutationMap U σ) hR
  have hSwap (p : Point (M := M) 2 0) : pointCell (vfPermutation σ p) = Prod.swap (pointCell p) := by
    simp only [pointCell,vfPermutation,Function.comp_apply,vfAt,σ,
      Equiv.swap_apply_left,Equiv.swap_apply_right,Prod.swap_prod_mk]
  convert h using 1
  ext p
  constructor
  · intro hp
    refine ⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩
    change pointCell (vfPermutation σ p) ∈ R
    rw [hSwap]
    exact hp
  · rintro ⟨a,ha,hp⟩
    change pointCell (vfPermutation σ a.val) ∈ R at hp
    rw [hSwap] at hp
    exact ha ▸ hp

end IntegrationInACVF.Section5
