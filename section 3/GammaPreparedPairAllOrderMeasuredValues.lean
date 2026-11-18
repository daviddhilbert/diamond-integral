import «section 3».GammaMatchingAllOrderMeasuredValues
import «section 3».GammaStandardLabelPartitionValues
import Integration7.PreparedPairContractionRestrictions
import Integration7.PreparedDifferentRectangleFamilies

/-! The translated matching-family contractions have the actual
prepared pullback Gamma classes, by the checked rectangle construction
and its exact retained-label equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation B (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames B ⊆ (C.base : Set M)}

theorem gammaPrepared_pair_all_order_measured_values
    (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))))
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction P.inFixedContext.wholePreparedPairFamily σ)
    (W : StandardContraction P.inFixedContext.wholePreparedPairFamily τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let Q := P.inFixedContext
    let hfinH := Q.whole_prepared_pair_family_finite_labels hfin
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.whole_prepared_pair_family_gamma hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.whole_prepared_pair_family_gamma hfinH W hW ω) := by
  intro Q hfinH
  obtain ⟨MT⟩ := Q.matching_pair_contraction_presentation T hT
  obtain ⟨DT⟩ := Q.different_pair_contraction_presentation T hT
  obtain ⟨MW⟩ := Q.matching_pair_contraction_presentation W hW
  obtain ⟨DW⟩ := Q.different_pair_contraction_presentation W hW
  let hfinM := Q.matching_prepared_family_finite_labels hfin
  let hfinD := Q.different_prepared_family_finite_labels hfin
  have hLeft := gammaStandard_binary_label_partition_values C hBC hNames
    Q.whole_prepared_pair_family_gamma Q.matching_prepared_family_gamma Q.different_prepared_family_gamma
    hfinH hfinM hfinD id Q.matchingPreparedRVLabels Q.matching_prepared_rv_labels_gamma
    Q.different_prepared_rv_labels_gamma T hT MT DT ω
  have hRight := gammaStandard_binary_label_partition_values C hBC hNames
    Q.whole_prepared_pair_family_gamma Q.matching_prepared_family_gamma Q.different_prepared_family_gamma
    hfinH hfinM hfinD id Q.matchingPreparedRVLabels Q.matching_prepared_rv_labels_gamma
    Q.different_prepared_rv_labels_gamma W hW MW DW ω
  have hMatch := gammaMatching_family_all_order_measured_values hBC hvf hg δ hδ hδ1 P hNonzero hfin ω
    MT.contraction MW.contraction MT.gamma MW.gamma
  have hDifferent := gammaRectangle_all_order_measured_values C hBC hvf hg hNames δ hδ hδ1
    Q.different_prepared_family_gamma hfinD Q.different_prepared_family_rectangular
    DT.contraction DW.contraction DT.gamma DW.gamma ω
  exact hLeft.trans ((congrArg₂ (· + ·) hMatch hDifferent).trans hRight.symm)

end DiamondIntegral.Section3
