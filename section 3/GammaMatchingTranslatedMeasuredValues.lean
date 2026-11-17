import «section 3».GammaMatchingContractionMeasuredValues

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

theorem gammaMatching_translated_measured_values
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
    (T : StandardContraction (extendBase P.inFixedContext.matchingVerticalImage P.inFixedContext.baseInclusion) σ)
    (W : StandardContraction (extendBase P.inFixedContext.matchingHorizontalImage P.inFixedContext.baseInclusion) τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let Q := P.inFixedContext
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    let hfinW := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_vertical_image_gamma hfinV T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_horizontal_image_gamma hfinW W hW ω) := by
  intro Q hr hfinH hfinV hfinW
  obtain ⟨LV,LH,⟨e⟩⟩ := gammaMatching_prepared_measured_comparison C hBC hvf P δ hδ1 hNonzero hfin
    (GammaGroundDefSet.univ hc B (rawRVSpace _)) (fun _ => Set.mem_univ _) ω
  have hLeft := gammaMatching_vertical_contraction_to_prepared_value hBC hvf hg δ hδ hδ1
    P hNonzero hfin ω LV T hT
  have hRight := gammaMatching_horizontal_contraction_to_prepared_value hBC hvf hg δ hδ hδ1
    P hNonzero hfin ω LH W hW
  exact hLeft.trans ((gammaMeasuredPrincipalValue_iso e).trans hRight.symm)

end DiamondIntegral.Section3
