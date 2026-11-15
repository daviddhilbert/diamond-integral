import IntegrationSection5.PositionedStripPreparation
import IntegrationSection5.CellStripNormalForms

/-! Constructed first stages in both coordinate orders for actual balanced
cells and for zero-paradigm cells with bijective positioning. -/
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

theorem balanced_cell_first_preparations (h : DefinableCellData G R f t) (hb : IsBalanced R f r t) :
    (∃ T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
        (fun p => positionInverse hb.2.2.1.bijective (vfAt p 1)), HeadSaturated (carrier T.target)) ∧
    (∃ T : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
        (fun p => f (vfAt p 1)), HeadSaturated (carrier T.target)) := by
  have hR := cellPointSet_gamma R h.2.1
  have hInv := positionInverse_gamma hb.2.2.1.bijective h.2.2.1
  constructor
  · apply positioned_strip_translation R (second R) (positionInverse hb.2.2.1.bijective) r
      (balanced_cell_horizontal_strip hb)
    · intro p hp q hq
      exact cell_first_rv_eq h.1 ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
    · exact balanced_horizontal_centre_rv h.1 hb
    · exact hR
    · exact hInv
  · apply positioned_strip_translation (swappedCell R) (first R) f t (swapped_cell_vertical_strip h.1)
    · intro p hp q hq
      exact cell_second_rv_eq h.1 ⟨Prod.swap p,hp,rfl⟩ ⟨Prod.swap q,hq,rfl⟩
    · intro p hp
      exact balanced_vertical_centre_rv h.1 hb (Prod.swap p) hp
    · exact swapped_cell_gamma hR
    · exact h.2.2.1

theorem graph_cell_first_preparations (h : DefinableCellData G R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) :
    (∃ T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
        (fun p => positionInverse (zero_paradigm_position_bijective h.1 ht hi) (vfAt p 1)),
      HeadSaturated (carrier T.target)) ∧
    (∃ T : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
        (fun p => f (vfAt p 1)), HeadSaturated (carrier T.target)) := by
  let H := zero_paradigm_position_bijective h.1 ht hi
  have hR := cellPointSet_gamma R h.2.1
  have hGraph := graph_of_zero_paradigm h.1 ht
  constructor
  · apply positioned_strip_translation R (second R) (positionInverse H) (rv (0 : VF (M := M)))
      (graph_cell_horizontal_strip h.1 ht hi)
    · intro p hp q hq
      exact cell_first_rv_eq h.1 ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
    · intro p hp
      have hg := (Set.ext_iff.mp hGraph p).mp hp
      rw [hg.2,positionInverse_left H p.1 hg.1]
    · exact hR
    · exact positionInverse_gamma H h.2.2.1
  · apply positioned_strip_translation (swappedCell R) (first R) f t (swapped_cell_vertical_strip h.1)
    · intro p hp q hq
      exact cell_second_rv_eq h.1 ⟨Prod.swap p,hp,rfl⟩ ⟨Prod.swap q,hq,rfl⟩
    · intro p hp
      have hg := (Set.ext_iff.mp hGraph (Prod.swap p)).mp hp
      exact congrArg rv hg.2.symm
    · exact swapped_cell_gamma hR
    · exact h.2.2.1

end IntegrationInACVF.Section5
