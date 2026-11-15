import IntegrationSection6.CommonHeadOrderComparison
import IntegrationSection6.ContractionOrderBridge

/-! Arbitrary contraction-order independence in RV[k], including selected
old RV volume labels. The only unfinished input is Section5.8. No Section6
independence or kernel statement is a hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem gamma_contraction_order_independent {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs) (n : ℕ) :
    ContractionOrderIndependent hκ.le hs h00 hreal n := by
  induction n with
  | zero =>
    intro a k U hU ρ hfin σ υ C E hC hE P Q
    have he : υ = σ := Subsingleton.elim _ _
    subst υ
    exact gamma_same_order_recursive_comparison hκ hs h00 hreal hgamma δ hδ hδ1 U hU ρ hfin σ C E hC hE P Q
  | succ n ih =>
    intro a k U hU ρ hfin σ υ C E hC hE P Q
    by_cases h0 : σ 0 = υ 0
    · exact gamma_common_head_order_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase ih
        U hU ρ hfin σ υ h0 C E hC hE P Q
    · cases n with
      | zero => exact False.elim (h0 (by apply Fin.ext; omega))
      | succ n =>
        obtain ⟨π,hπ0,hπ1⟩ := exists_contraction_bridge_order σ υ h0
        obtain ⟨D,hD,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
          (Set.subset_univ _) U hU π
        obtain ⟨F,hF,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
          (Set.subset_univ _) U hU ((swapFirstTwo n).trans π)
        obtain ⟨R⟩ := gammaSelectedRVPresentation_exists D.target (gamma_program_final_set D.program hD)
          (orderedSelectedIndex D.program ρ)
          (ordered_selected_fibres_finite hκ.le hs hreal D.program hD ρ (vfPermutation_selected_finite U π ρ hfin))
        obtain ⟨T⟩ := gammaSelectedRVPresentation_exists F.target (gamma_program_final_set F.program hF)
          (orderedSelectedIndex F.program ρ)
          (ordered_selected_fibres_finite hκ.le hs hreal F.program hF ρ
            (vfPermutation_selected_finite U ((swapFirstTwo n).trans π) ρ hfin))
        have H1 := gamma_common_head_order_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase ih
          U hU ρ hfin σ π hπ0.symm C D hC hD P R
        have hFirst : ((swapFirstTwo n).trans π) 0 = υ 0 := by
          change π (swapFirstTwo n 0) = υ 0
          rw [swapFirstTwo_zero]
          exact hπ1
        have H3 := gamma_common_head_order_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase ih
          U hU ρ hfin ((swapFirstTwo n).trans π) υ hFirst F E hF hE T Q
        have H := lemma_6_16_selected_univ hκ hs h00 hreal hgamma δ hδ hδ1
          (fun t x => h58
            ⟨(B.real ∪ Set.range (fun j => (t j).val)) ∪ Set.range (fun j => (x j).val),B.gamma⟩
            _ hκ h00 δ hδ hδ1) U hU ρ hfin D F hD hF
        have Hcast := H.castDegree (orderedVolumeDegree_eq (n+2) k).symm
        have H2 := Hcast.corollary_6_6
          (gammaContractionPresentationIso hκ.le hs hreal (Set.subset_univ _) hU ρ hfin D hD R)
          (gammaContractionPresentationIso hκ.le hs hreal (Set.subset_univ _) hU ρ hfin F hF T)
        exact H1.trans (H2.trans H3)

end IntegrationInACVF.Section6.FiniteRV
