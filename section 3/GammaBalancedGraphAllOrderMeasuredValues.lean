import «section 3».GammaPreparedPairAllOrderMeasuredValues
import «section 3».GammaRVGraphRefinementMeasuredValues
import Integration7.GeneratedBaseStandardContractions

/-! Record both prepared keys using the existing RV graph refinement,
compare its matching and different parts, and return through the actual
VF-fixed maps with the original retained Gamma form. -/
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

theorem gammaBalanced_graph_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {m : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (F : UniformMixedCellPresentation B (carrier A)) (hBalanced : F.BalancedRows)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) (m+F.arity))))
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (W : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let H := gammaRVGraphRefinement A F.parameters hNames
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hH hfinH W hW ω) := by
  intro H hH hfinH
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  obtain ⟨P⟩ := uniform_balanced_position_preparation_exists C hBC hNames δ hδ hδ1 F hBalanced
  let Q := P.inFixedContext
  obtain ⟨R,hR,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr hGenerated hBC
    Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma σ
  obtain ⟨S,hS,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr hGenerated hBC
    Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma τ
  let η := gammaTotalRVCoordinateForm (Fin.castAdd ((1+Q.sourceArity)+(1+Q.targetArity))) ω
  have hMiddle := gammaPrepared_pair_all_order_measured_values hBC hv hg δ hδ hδ1 P hNonzero hfin η R S hR hS
  have hLeft := gammaRVGraph_refinement_measured_values C hBC hv hg hNames δ hδ hδ1
    H hH hfinH Q.pairKeyLabels ω T R hT hR
  have hRight := gammaRVGraph_refinement_measured_values C hBC hv hg hNames δ hδ hδ1
    H hH hfinH Q.pairKeyLabels ω W S hW hS
  exact hLeft.trans (hMiddle.trans hRight.symm)

end DiamondIntegral.Section3
