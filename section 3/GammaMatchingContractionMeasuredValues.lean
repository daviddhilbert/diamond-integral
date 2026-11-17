import «section 3».GammaRectanglePullbackMeasuredValues
import «section 3».GammaNativePullbackTotalForms
import Integration7.MatchingPreparedUnaryRelative
import Integration7.LabelDeterminedPullbackRectangles

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

theorem gammaMatching_vertical_contraction_to_prepared_value
    (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))))
    (L : PreparedKeyLabelSpecialPreparation P.inFixedContext.sourceSpecial
      (extendBase P.inFixedContext.matchingVerticalTailDomain P.inFixedContext.baseInclusion)
      P.inFixedContext.matchingOldLabelIndex P.inFixedContext.matchingTailKeyIndex
      (fun p hp => P.inFixedContext.matching_vertical_tail_old_mem ⟨p,hp⟩) B)
    {σ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingVerticalImage P.inFixedContext.baseInclusion) σ)
    (hT : GammaProgramDefinable B T.program) :
    let Q := P.inFixedContext
    let PV := Q.matchingVerticalPullbackPreparation hNonzero L
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_vertical_image_gamma hfinV T hT ω) =
      gammaMeasuredPrincipalValue (gammaPreparedRectangleRVObject C hBC PV
        P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma P.matching_fixed_vertical_labels hfinH
        (GammaGroundDefSet.univ hc B (rawRVSpace _)) (fun _ => Set.mem_univ _) ω) := by
  intro Q PV hr hfinH hfinV
  have hAF := PV.finite_volume C.uncountable.le C.saturated hr
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
  have hfinTarget := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
    (SpecialTransformations.Section5.Map.comp PV.volumeMap P.matchingFixedVerticalMap)
    (PV.volume_map_bijective.comp P.matching_fixed_vertical_bijective)
    (gamma_composition_graph _ _ P.matching_fixed_vertical_gamma PV.volume_graph_gamma) hfinH
  let η := gammaTotalRVCoordinateForm PV.volumeLabelIndex ω
  have hForm (p : extendBase Q.matchingVerticalImage Q.baseInclusion) :
      η ⟨(PV.volumeMap p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩ := by
    apply congrArg ω
    apply Subtype.ext
    funext i
    exact PV.volume_old_labels p i
  have h := gammaRectangle_contraction_to_pullback_value C hBC hvf hg hNames δ hδ hδ1
    Q.matching_vertical_image_gamma PV.volume_target_gamma hfinV hfinTarget
    (Q.matching_vertical_image_rectangular hNonzero) (Q.matching_vertical_prepared_rectangular hNonzero L)
    PV.volume_target_pullback hAF ω η PV.volumeMap PV.volume_map_bijective PV.volume_graph_gamma
    hForm (PV.volume_jacobian_one hc C) (Equiv.swap 0 1) (Q.matching_vertical_prepared_unary_relative hNonzero L) T hT
  have he := gammaPreparedRectangle_total_object C hBC PV P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matching_fixed_vertical_gamma P.matching_fixed_vertical_labels hfinH ω
  exact h.trans (congrArg gammaMeasuredPrincipalValue he).symm

theorem gammaMatching_horizontal_contraction_to_prepared_value
    (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))))
    (L : PreparedKeyLabelSpecialPreparation P.inFixedContext.targetSpecial
      (extendBase P.inFixedContext.matchingHorizontalHeadDomain P.inFixedContext.baseInclusion)
      P.inFixedContext.matchingOldLabelIndex P.inFixedContext.matchingHeadKeyIndex
      (fun p hp => P.inFixedContext.matching_horizontal_head_old_mem ⟨p,hp⟩) B)
    {σ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingHorizontalImage P.inFixedContext.baseInclusion) σ)
    (hT : GammaProgramDefinable B T.program) :
    let Q := P.inFixedContext
    let PV := Q.matchingHorizontalPullbackPreparation hNonzero L
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_horizontal_image_gamma hfinV T hT ω) =
      gammaMeasuredPrincipalValue (gammaPreparedRectangleRVObject C hBC PV
        P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma P.matching_fixed_horizontal_labels hfinH
        (GammaGroundDefSet.univ hc B (rawRVSpace _)) (fun _ => Set.mem_univ _) ω) := by
  intro Q PV hr hfinH hfinV
  have hAF := PV.finite_volume C.uncountable.le C.saturated hr
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
  have hfinTarget := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
    (SpecialTransformations.Section5.Map.comp PV.volumeMap P.matchingFixedHorizontalMap)
    (PV.volume_map_bijective.comp P.matching_fixed_horizontal_bijective)
    (gamma_composition_graph _ _ P.matching_fixed_horizontal_gamma PV.volume_graph_gamma) hfinH
  let η := gammaTotalRVCoordinateForm PV.volumeLabelIndex ω
  have hForm (p : extendBase Q.matchingHorizontalImage Q.baseInclusion) :
      η ⟨(PV.volumeMap p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩ := by
    apply congrArg ω
    apply Subtype.ext
    funext i
    exact PV.volume_old_labels p i
  have h := gammaRectangle_contraction_to_pullback_value C hBC hvf hg hNames δ hδ hδ1
    Q.matching_horizontal_image_gamma PV.volume_target_gamma hfinV hfinTarget
    (Q.matching_horizontal_image_rectangular hNonzero) (Q.matching_horizontal_prepared_rectangular hNonzero L)
    PV.volume_target_pullback hAF ω η PV.volumeMap PV.volume_map_bijective PV.volume_graph_gamma
    hForm (PV.volume_jacobian_one hc C) (Equiv.refl _) (Q.matching_horizontal_prepared_unary_relative hNonzero L) T hT
  have he := gammaPreparedRectangle_total_object C hBC PV P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_horizontal_gamma P.matching_fixed_horizontal_labels hfinH ω
  exact h.trans (congrArg gammaMeasuredPrincipalValue he).symm

end DiamondIntegral.Section3
