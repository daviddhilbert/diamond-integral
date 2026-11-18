import «section 3».GammaMatchingTranslatedMeasuredValues
import «section 3».GammaRelativeRetainedContractionValues
import Integration7.MixedTranslationContractionComparisons

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

theorem gammaMatching_family_opposite_measured_values
    (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (P : UniformBalancedPositionPreparation B C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M)
      ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))))
    (T : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) (Equiv.refl _))
    (W : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let Q := P.inFixedContext
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_prepared_family_gamma hfinH T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC Q.matching_prepared_family_gamma hfinH W hW ω) := by
  intro Q hfinH
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let H := extendBase Q.matchingPreparedFamily Q.baseInclusion
  let V := extendBase Q.matchingVerticalImage Q.baseInclusion
  let Y := extendBase Q.matchingHorizontalImage Q.baseInclusion
  have hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
  have hfinY := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hr
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
  obtain ⟨FV⟩ := independent_rectangle_family_preparations_exists C hNames δ hδ hδ1 V
    Q.matching_vertical_image_gamma (Q.matching_vertical_image_rectangular hNonzero)
  obtain ⟨FY⟩ := independent_rectangle_family_preparations_exists C hNames δ hδ hδ1 Y
    Q.matching_horizontal_image_gamma (Q.matching_horizontal_image_rectangular hNonzero)
  let R := FV.headContraction
  let S := FY.tailContraction
  have hR := FV.head_contraction_gamma Q.matching_vertical_image_gamma
  have hS := FY.tail_contraction_gamma Q.matching_horizontal_image_gamma
  have hvForm (p : H) : ω ⟨(P.matchingFixedVerticalMap p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩ :=
    congrArg ω (Subtype.ext (P.matching_fixed_vertical_labels p))
  have hhForm (p : H) : ω ⟨(P.matchingFixedHorizontalMap p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩ :=
    congrArg ω (Subtype.ext (P.matching_fixed_horizontal_labels p))
  have hiV : UnaryRelative P.matchingFixedVerticalMap ((Equiv.refl (Fin 2)) 0) :=
    relative_translation_unary_relative Q.matchingPreparedFamily 0 Q.matchingVerticalCentre
  have hiY : UnaryRelative P.matchingFixedHorizontalMap ((Equiv.swap (0 : Fin 2) 1) 0) :=
    relative_translation_unary_relative Q.matchingPreparedFamily 1 Q.matchingHorizontalCentre
  have hLeft := gammaRelative_retained_contraction_values C hBC hvf hg δ hδ hδ1
    Q.matching_prepared_family_gamma Q.matching_vertical_image_gamma hfinH hfinV ω ω
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hvForm
    (P.matching_fixed_vertical_jacobian_one hc) hiV T R hT hR
  have hRight := gammaRelative_retained_contraction_values C hBC hvf hg δ hδ hδ1
    Q.matching_prepared_family_gamma Q.matching_horizontal_image_gamma hfinH hfinY ω ω
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hhForm
    (P.matching_fixed_horizontal_jacobian_one hc) hiY W S hW hS
  have hMiddle := gammaMatching_translated_measured_values hBC hvf hg δ hδ hδ1 P hNonzero hfin ω R S hR hS
  exact hLeft.trans (hMiddle.trans hRight.symm)

end DiamondIntegral.Section3
