import «section 3».GammaBalancedGraphAllOrderMeasuredValues
import «section 3».GammaSmallDimensionContractionValues
import «section 3».GammaStandardLabelPartitionValues
import Integration7.UniformCellShapePartitionArrays
import Integration7.SelectedBalancedParadigms

/-! The original zero, rectangle and balanced cell-family pieces
assemble with actual Gamma measured scissors. Every retained density
is unchanged throughout the existing two-coordinate construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaCell_graph_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {m : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (F : UniformMixedCellPresentation B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) (m+F.arity))))
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (W : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH W hW ω) := by
  intro hH hfinH
  let P := F.shapeNativePieces hNames
  let R := F.shapeRVLabels hNames
  let hP := F.shape_native_piece_gamma hNames
  let hR := F.shape_rv_labels_gamma hNames
  let hfinP := F.shape_native_piece_finite_labels hNames hfin
  let DT (i : Fin 3) := Classical.choice (F.shape_contraction_presentations hNames T hT i)
  let DW (i : Fin 3) := Classical.choice (F.shape_contraction_presentations hNames W hW i)
  have hCover : ∀ r : Point (M := M) 0 (m+F.arity), ∃ i, r ∈ R i := by
    intro r
    have hr : r ∈ (R 0 ∪ R 1) ∪ R 2 := by rw [F.shape_rv_labels_cover hNames]; exact Set.mem_univ _
    rcases hr with (hr | hr) | hr
    · exact ⟨0,hr⟩
    · exact ⟨1,hr⟩
    · exact ⟨2,hr⟩
  have hDisj : ∀ i j, i ≠ j → Disjoint (R i) (R j) := fun _ _ hij => F.shape_rv_labels_disjoint hNames hij
  have hLeft := gammaStandard_label_partition_values C hBC hNames P hH hP hfinH hfinP id R hR hDisj hCover T hT DT ω
  have hRight := gammaStandard_label_partition_values C hBC hNames P hH hP hfinH hfinP id R hR hDisj hCover W hW DW ω
  have hCompare (i : Fin 3) :
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (hP i) (hfinP i) (DT i).contraction (DT i).gamma ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (hP i) (hfinP i) (DW i).contraction (DW i).gamma ω) := by
    fin_cases i
    · have hSmall := (F.zero_native_part_dimension hc hNames).trans_lt (by decide : 1 < 2)
      have hZeroT := gammaSmall_dimension_contraction_value C hBC (F.zeroNativePart hNames)
        (F.zero_native_part_gamma hNames) (F.zero_native_part_finite_labels hNames hfin)
        (DT 0).contraction (DT 0).gamma hSmall ω
      have hZeroW := gammaSmall_dimension_contraction_value C hBC (F.zeroNativePart hNames)
        (F.zero_native_part_gamma hNames) (F.zero_native_part_finite_labels hNames hfin)
        (DW 0).contraction (DW 0).gamma hSmall ω
      exact hZeroT.trans hZeroW.symm
    · exact gammaRectangle_all_order_measured_values C hBC hv hg hNames δ hδ hδ1
        (F.rectangular_native_part_gamma hNames) (F.rectangular_native_part_finite_labels hNames hfin)
        (F.rectangular_native_part_fibres hNames) (DT 1).contraction (DW 1).contraction (DT 1).gamma (DW 1).gamma ω
    · exact gammaBalanced_graph_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1
        (F.balancedNativeChart hNames) (F.balanced_native_chart_rows hNames δ hδ1)
        (F.balanced_native_chart_paradigm_nonzero hNames) (F.balanced_native_source_finite_labels hNames hfin)
        ω (DT 2).contraction (DW 2).contraction (DT 2).gamma (DW 2).gamma
  exact hLeft.trans ((Finset.sum_congr rfl (fun i _ => hCompare i)).trans hRight.symm)

end DiamondIntegral.Section3
