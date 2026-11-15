import IntegrationSection5.CellStandardPresentation

/-! Lemma 5.7 for balanced cells and zero-paradigm graph cells with
injective positioning, using actual standard contractions in both orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem lemma_5_7_balanced {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (hb : IsBalanced R f r t) :
    ∃ W : Set M, ∃ AR : DefSet (M := M) W 2 0, carrier AR = cellPointSet R ∧
      ∃ C12 : StandardContraction AR (Equiv.refl _),
      ∃ C21 : StandardContraction AR (Equiv.swap 0 1),
        Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  obtain ⟨TH,hTH,TV,hTV,Q,_,_,⟨e⟩⟩ :=
    balanced_cell_staged_contractions hκ hs hsmall h00 δ hδ hδ1 F h hb
  exact cell_standard_pair_of_matched TH.source_eq TV.source_eq Q e

theorem lemma_5_7_bijective_graph {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (h : DefinableCellData G R f t) (ht : t = rv (0 : VF (M := M)))
    (hi : Set.InjOn f (first R)) :
    ∃ W : Set M, ∃ AR : DefSet (M := M) W 2 0, carrier AR = cellPointSet R ∧
      ∃ C12 : StandardContraction AR (Equiv.refl _),
      ∃ C21 : StandardContraction AR (Equiv.swap 0 1),
        Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  obtain ⟨TH,hTH,TV,hTV,Q,_,_,⟨e⟩⟩ :=
    graph_cell_staged_contractions hκ hs hsmall h00 δ hδ hδ1 F h ht hi
  exact cell_standard_pair_of_matched TH.source_eq TV.source_eq Q e

end IntegrationInACVF.Section5
