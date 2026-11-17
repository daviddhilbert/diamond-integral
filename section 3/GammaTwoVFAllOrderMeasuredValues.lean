import «section 3».GammaCellGraphAllOrderMeasuredValues
import Integration7.GeneratedBaseStandardContractions

/-! The two-coordinate order comparison uses the original actual cell
preparation and RV graph refinement. Its zero, rectangle and balanced
cases preserve arbitrary retained original-Gamma densities. -/
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
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaTwo_VF_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {a : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin W hW ω) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  obtain ⟨F⟩ := uniform_mixed_cell_presentation_exists C.uncountable.le C.saturated C.model00 hr
    hGenerated δ hδ hδ1 hA
  let H := gammaRVGraphRefinement A F.parameters hNames
  let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
  let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
  obtain ⟨R,hR,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr hGenerated hBC H hH σ
  obtain ⟨S,hS,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr hGenerated hBC H hH τ
  let η := gammaTotalRVCoordinateForm (Fin.castAdd F.arity) ω
  have hMiddle := gammaCell_graph_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1 F hfin η R S hR hS
  have hLeft := gammaRVGraph_refinement_measured_values C hBC hv hg hNames δ hδ hδ1 A hA hfin F.parameters ω T R hT hR
  have hRight := gammaRVGraph_refinement_measured_values C hBC hv hg hNames δ hδ hδ1 A hA hfin F.parameters ω W S hW hS
  exact hLeft.trans (hMiddle.trans hRight.symm)

end DiamondIntegral.Section3
