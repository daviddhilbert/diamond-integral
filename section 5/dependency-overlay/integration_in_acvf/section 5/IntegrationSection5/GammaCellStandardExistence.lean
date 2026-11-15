import IntegrationSection5.GammaBalancedCellComparison
import IntegrationSection5.GammaProductCellComparison
import IntegrationSection5.CellRectangleStandard

/-! Full original-Gamma Lemma 5.7. Both actual standard programs and both
directions of the actual RV[2] isomorphism are constructed and certified. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))}

theorem lemma_5_7_gamma_cell_data {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (h : DefinableCellData G R f t) : Nonempty (GammaCellStandardComparison G R) := by
  by_cases hBalanced : ∃ r, IsBalanced R f r t
  · obtain ⟨r,hr⟩ := hBalanced
    exact gamma_balanced_cell_comparison hκ hs hsmall h00 δ hδ hδ1 F h hr
  · by_cases ht : t = rv (0 : VF (M := M))
    · rcases cell_position_constant_or_injective h.1 with hc | hi
      · exact gamma_rectangle_cell_comparison hs h00 hsmall F R (cellPointSet_gamma R h.2.1)
          (constant_position_rectangle h.1 hc)
      · exact gamma_bijective_graph_comparison hκ hs hsmall h00 δ hδ hδ1 F h ht hi
    · obtain ⟨E,hE,hRect⟩ := CellRectangles.rectangle δ hδ1 h.1 ht hBalanced
      exact gamma_rectangle_cell_comparison hs h00 hsmall F R (cellPointSet_gamma R h.2.1)
        (rectangle_eq_projections _ E hRect)

theorem lemma_5_7_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableTwoCell G R) : Nonempty (GammaCellStandardComparison G R) := by
  obtain ⟨f,t,h⟩ := h
  exact lemma_5_7_gamma_cell_data hκ hs hsmall h00 δ hδ hδ1 F h

end IntegrationInACVF.Section5
