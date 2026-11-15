import IntegrationSection5.GammaCellComparison

/-! Full original-Gamma cell comparison for the balanced and bijective
graph cases, retaining the actual RV[2] maps in both directions. -/
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

theorem balanced_paradigm_absorbing_iff (h : CellData R f t) (hb : IsBalanced R f r t) :
    t.val = iRVZero ↔ r.val = iRVZero := by
  obtain ⟨p,hp⟩ := CellRectangles.nonempty h
  have he := paradigms_degenerate_together hb.2.2.1 p.1 ⟨p,hp,rfl⟩
  have hz (z : RV (M := M)) : z.val = iRVZero ↔ z = rv (0 : VF (M := M)) := by
    have h0 : (rv (0 : VF (M := M))).val = iRVZero := (CanonicalRV.encodedRv_zero_iff _).mpr rfl
    exact ⟨fun h => Subtype.ext (h.trans h0.symm),fun h => (congrArg Subtype.val h).trans h0⟩
  exact (hz t).trans (he.symm.trans (hz r).symm)

theorem gamma_balanced_cell_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (hb : IsBalanced R f r t) :
    Nonempty (GammaCellStandardComparison G R) := by
  obtain ⟨TH,hTH,TV,hTV,Q,_,_,_⟩ := balanced_cell_staged_contractions hκ hs hsmall h00 δ hδ hδ1 F h hb
  let e := Q.gammaRVIso t r (balanced_paradigm_absorbing_iff h.1 hb)
    (strip_contraction_constant_label (first R) t (swapped_cell_vertical_strip h.1) TV hTV)
    (strip_contraction_constant_label (second R) r (balanced_cell_horizontal_strip hb) TH hTH)
  exact gamma_cell_pair_of_matched TH.real_contains TH.source_eq TV.source_eq
    (TH.source_eq.symm ▸ cellPointSet_gamma R h.2.1)
    TV.graph TV.target_gamma TH.graph TH.target_gamma Q e

theorem gamma_bijective_graph_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) : Nonempty (GammaCellStandardComparison G R) := by
  obtain ⟨TH,hTH,TV,hTV,Q,_,_,_⟩ := graph_cell_staged_contractions hκ hs hsmall h00 δ hδ hδ1 F h ht hi
  let e := Q.gammaRVIso t (rv (0 : VF (M := M))) (by rw [ht])
    (strip_contraction_constant_label (first R) t (swapped_cell_vertical_strip h.1) TV hTV)
    (strip_contraction_constant_label (second R) (rv (0 : VF (M := M)))
      (graph_cell_horizontal_strip h.1 ht hi) TH hTH)
  exact gamma_cell_pair_of_matched TH.real_contains TH.source_eq TV.source_eq
    (TH.source_eq.symm ▸ cellPointSet_gamma R h.2.1)
    TV.graph TV.target_gamma TH.graph TH.target_gamma Q e

end IntegrationInACVF.Section5
