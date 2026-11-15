import IntegrationSection5.CellContractedBijection
import IntegrationSection5.MatchedHeadRV
import IntegrationSection4.CellRectangles

/-! Constructed two-stage programs and actual RV[2] comparison for the
balanced and bijective graph cases of Lemma 5.7. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section4.BalancedFibres
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem balanced_cell_staged_contractions {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (hb : IsBalanced R f r t) :
    ∃ TH : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
        (fun p => positionInverse hb.2.2.1.bijective (vfAt p 1)),
    ∃ hTH : HeadSaturated (carrier TH.target),
    ∃ TV : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
        (fun p => f (vfAt p 1)),
    ∃ hTV : HeadSaturated (carrier TV.target),
    ∃ Q : MatchedHeadCompletion (G := G) (TV.toHead hTV) (TH.toHead hTH),
      GammaProgramDefinable G Q.programA ∧ GammaProgramDefinable G Q.programB ∧
      Nonempty (Q.objectA ≅ Q.objectB) := by
  obtain ⟨⟨TH,hTH⟩,⟨TV,hTV⟩⟩ := balanced_cell_first_preparations h hb
  obtain ⟨Q⟩ := matched_head_completion hκ hs hsmall h00 δ hδ hδ1 F _ _
    (strip_contractedSet_gamma TV hTV) (strip_contractedSet_gamma TH hTH)
    (balanced_contracted_unary_iso h hb TH hTH TV hTV)
  have ht : t.val = iRVZero ↔ r.val = iRVZero := by
    obtain ⟨p,hp⟩ := CellRectangles.nonempty h.1
    have he := paradigms_degenerate_together hb.2.2.1 p.1 ⟨p,hp,rfl⟩
    have hz (z : RV (M := M)) : z.val = iRVZero ↔ z = rv (0 : VF (M := M)) := by
      have h0 : (rv (0 : VF (M := M))).val = iRVZero :=
        (CanonicalRV.encodedRv_zero_iff _).mpr rfl
      exact ⟨fun h => Subtype.ext (h.trans h0.symm),fun h => (congrArg Subtype.val h).trans h0⟩
    exact (hz t).trans (he.symm.trans (hz r).symm)
  exact ⟨TH,hTH,TV,hTV,Q,Q.programA_gamma TV.graph TV.target_gamma,
    Q.programB_gamma TH.graph TH.target_gamma,
    ⟨Q.rvIso t r ht
      (strip_contraction_constant_label (first R) t (swapped_cell_vertical_strip h.1) TV hTV)
      (strip_contraction_constant_label (second R) r (balanced_cell_horizontal_strip hb) TH hTH)⟩⟩

theorem graph_cell_staged_contractions {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) :
    ∃ TH : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
        (fun p => positionInverse (zero_paradigm_position_bijective h.1 ht hi) (vfAt p 1)),
    ∃ hTH : HeadSaturated (carrier TH.target),
    ∃ TV : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
        (fun p => f (vfAt p 1)),
    ∃ hTV : HeadSaturated (carrier TV.target),
    ∃ Q : MatchedHeadCompletion (G := G) (TV.toHead hTV) (TH.toHead hTH),
      GammaProgramDefinable G Q.programA ∧ GammaProgramDefinable G Q.programB ∧
      Nonempty (Q.objectA ≅ Q.objectB) := by
  obtain ⟨⟨TH,hTH⟩,⟨TV,hTV⟩⟩ := graph_cell_first_preparations h ht hi
  obtain ⟨Q⟩ := matched_head_completion hκ hs hsmall h00 δ hδ hδ1 F _ _
    (strip_contractedSet_gamma TV hTV) (strip_contractedSet_gamma TH hTH)
    (graph_contracted_unary_iso h ht hi TH hTH TV hTV)
  exact ⟨TH,hTH,TV,hTV,Q,Q.programA_gamma TV.graph TV.target_gamma,
    Q.programB_gamma TH.graph TH.target_gamma,
    ⟨Q.rvIso t (rv (0 : VF (M := M))) (by rw [ht])
      (strip_contraction_constant_label (first R) t (swapped_cell_vertical_strip h.1) TV hTV)
      (strip_contraction_constant_label (second R) (rv (0 : VF (M := M)))
        (graph_cell_horizontal_strip h.1 ht hi) TH hTH)⟩⟩

end IntegrationInACVF.Section5
