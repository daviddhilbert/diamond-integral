import IntegrationSection5.CellFirstPreparations
import IntegrationSection5.StripContractionGeometry
import IntegrationSection5.UnaryPresentationBijection
import IntegrationSection5.MatchedUnaryPreparation

/-! The two actual first contractions of a balanced cell, or a graph cell
with bijective positioning, are joined by the actual positioning bijection.
Matched unary tails are constructed by the full Lemmas 5.2 and 5.3. -/
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

def balanced_contracted_unary_iso (h : DefinableCellData G R f t) (hb : IsBalanced R f r t)
    (TH : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
      (fun p => positionInverse hb.2.2.1.bijective (vfAt p 1)))
    (hTH : HeadSaturated (carrier TH.target))
    (TV : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
      (fun p => f (vfAt p 1))) (hTV : HeadSaturated (carrier TV.target)) :
    GammaIso G (carrier (TV.toHead hTV).contractedSet) (carrier (TH.toHead hTH).contractedSet) := by
  apply unaryPresentationGammaIso _ _ (strip_contractedSet_gamma TV hTV)
    (strip_contractedSet_gamma TH hTH) (first R) (second R)
  · apply strip_contraction_vf_bijective (first R) t (swapped_cell_vertical_strip h.1) _ TV hTV
    intro p hp q hq
    exact cell_second_rv_eq h.1 ⟨Prod.swap p,hp,rfl⟩ ⟨Prod.swap q,hq,rfl⟩
  · apply strip_contraction_vf_bijective (second R) r (balanced_cell_horizontal_strip hb) _ TH hTH
    intro p hp q hq
    exact cell_first_rv_eq h.1 ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
  · exact hb.2.2.1.bijective
  · exact h.2.2.1

def graph_contracted_unary_iso (h : DefinableCellData G R f t)
    (ht : t = rv (0 : VF (M := M))) (hi : Set.InjOn f (first R))
    (TH : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0
      (fun p => positionInverse (zero_paradigm_position_bijective h.1 ht hi) (vfAt p 1)))
    (hTH : HeadSaturated (carrier TH.target))
    (TV : CanonicalTranslationPreparation (G := G) (cellPointSet (swappedCell R)) 0
      (fun p => f (vfAt p 1))) (hTV : HeadSaturated (carrier TV.target)) :
    GammaIso G (carrier (TV.toHead hTV).contractedSet) (carrier (TH.toHead hTH).contractedSet) := by
  apply unaryPresentationGammaIso _ _ (strip_contractedSet_gamma TV hTV)
    (strip_contractedSet_gamma TH hTH) (first R) (second R)
  · apply strip_contraction_vf_bijective (first R) t (swapped_cell_vertical_strip h.1) _ TV hTV
    intro p hp q hq
    exact cell_second_rv_eq h.1 ⟨Prod.swap p,hp,rfl⟩ ⟨Prod.swap q,hq,rfl⟩
  · apply strip_contraction_vf_bijective (second R) (rv (0 : VF (M := M)))
      (graph_cell_horizontal_strip h.1 ht hi) _ TH hTH
    intro p hp q hq
    exact cell_first_rv_eq h.1 ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
  · exact zero_paradigm_position_bijective h.1 ht hi
  · exact h.2.2.1

theorem balanced_cell_matched_tails {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
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
      Nonempty (MatchedUnaryPreparation (G := G)
        (carrier (TV.toHead hTV).contractedSet) (carrier (TH.toHead hTH).contractedSet)
        (balanced_contracted_unary_iso h hb TH hTH TV hTV).equiv) := by
  obtain ⟨⟨TH,hTH⟩,⟨TV,hTV⟩⟩ := balanced_cell_first_preparations h hb
  exact ⟨TH,hTH,TV,hTV,matched_unary_preparation hκ hs hsmall h00 δ hδ hδ1 F _ _
    (strip_contractedSet_gamma TV hTV) (strip_contractedSet_gamma TH hTH)
    (balanced_contracted_unary_iso h hb TH hTH TV hTV)⟩

theorem graph_cell_matched_tails {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
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
      Nonempty (MatchedUnaryPreparation (G := G)
        (carrier (TV.toHead hTV).contractedSet) (carrier (TH.toHead hTH).contractedSet)
        (graph_contracted_unary_iso h ht hi TH hTH TV hTV).equiv) := by
  obtain ⟨⟨TH,hTH⟩,⟨TV,hTV⟩⟩ := graph_cell_first_preparations h ht hi
  exact ⟨TH,hTH,TV,hTV,matched_unary_preparation hκ hs hsmall h00 δ hδ hδ1 F _ _
    (strip_contractedSet_gamma TV hTV) (strip_contractedSet_gamma TH hTH)
    (graph_contracted_unary_iso h ht hi TH hTH TV hTV)⟩

end IntegrationInACVF.Section5
